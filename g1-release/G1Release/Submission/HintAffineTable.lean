import G1Release.Submission.BinaryFieldHint
import G1Release.Submission.HintPayload

namespace G1Release.Submission.HintAffineTable

open GarblingPrize.Protected
open scoped BigOperators

abbrev Purpose := Nat
/-- Oracle-derived pad families, not the challenge input labels. -/
abbrev PadFamily := Purpose → SecretRelease.Label

abbrev Word := HintPayload.Word
abbrev WordBytes := HintPayload.WordBytes
abbrev Params := HintPayload.Params
abbrev Ciphertext := HintPayload.Ciphertext
abbrev Coin := Fin (4 * BinaryFieldHint.modulus)
abbrev RowIndex := Fin HintPayload.tableWidth

abbrev tableWordCount : Nat := HintPayload.tableWidth + 1
def tableByteCount : Nat := tableWordCount * 32

/-- A concrete vector keeps each row shared throughout encoding. A function
representation can cause native eta expansion to rebuild a table per lookup. -/
structure Table where
  storage : Vector WordBytes tableWordCount

def Table.words (table : Table) (index : Fin tableWordCount) : WordBytes :=
  table.storage[index.val]

def Table.ofWords (words : Fin tableWordCount → WordBytes) : Table :=
  ⟨Vector.ofFn words⟩

@[simp] theorem Table.words_ofWords (words : Fin tableWordCount → WordBytes) :
    (Table.ofWords words).words = words := by
  funext index
  simp [Table.words, Table.ofWords]

@[simp] theorem Table.words_ofWords_apply (words : Fin tableWordCount → WordBytes)
    (index : Fin tableWordCount) : (Table.ofWords words).words index = words index :=
  congrFun (Table.words_ofWords words) index

@[ext] theorem Table.ext (left right : Table) (hwords : left.words = right.words) :
    left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      congr 1
      apply Vector.ext
      intro index hindex
      exact congrFun hwords ⟨index, hindex⟩

@[simp] theorem Table.ofWords_words (table : Table) : Table.ofWords table.words = table := by
  apply Table.ext
  exact Table.words_ofWords table.words

/-- Direct indexing of a header followed by rows.  The equation to `Fin.cases`
below identifies the same finite sequence; the executable branch avoids the
induction recursor's evaluation of every preceding row. -/
def prependWord (first : WordBytes) (rest : RowIndex → WordBytes)
    (index : Fin tableWordCount) : WordBytes :=
  if h : index.val = 0 then first
  else rest ⟨index.val - 1, by
    have hi : index.val < HintPayload.tableWidth + 1 := index.isLt
    omega⟩

@[simp] theorem prependWord_eq_cases (first : WordBytes) (rest : RowIndex → WordBytes) :
    prependWord first rest = Fin.cases first rest := by
  funext index
  refine Fin.cases ?_ (fun row => ?_) index
  · simp [prependWord]
  · simp [prependWord, Fin.val_succ]

theorem modulus_positive : 0 < BinaryFieldHint.modulus := by
  norm_num [BinaryFieldHint.modulus, baseFieldModulus]

theorem rangeSize_eq :
    BinaryFieldHint.rangeSize BinaryFieldHint.modulus BinaryFieldHint.remainder =
      BinaryFieldHint.binaryRange := by
  have := BinaryFieldHint.concrete_range
  dsimp [BinaryFieldHint.rangeSize, BinaryFieldHint.remainder]
  omega

def keyFromPad (pad : WordBytes) :
    BinaryFieldHint.Key BinaryFieldHint.modulus BinaryFieldHint.remainder :=
  (BinaryFieldHint.keyEquiv _ _).symm
    ⟨HintCodec.decodeNatLE pad % BinaryFieldHint.binaryRange, by
      rw [rangeSize_eq]
      exact Nat.mod_lt _ (by dsimp [BinaryFieldHint.binaryRange]; positivity)⟩

def padHint (pad : WordBytes) (coin : Coin) : Bool :=
  (BinaryFieldHint.sample modulus_positive BinaryFieldHint.concrete_remainder.1
    (keyFromPad pad) coin).2

def maskFromPad (pad : WordBytes) (hint : Bool) : Word :=
  ((BinaryFieldHint.endpoint modulus_positive BinaryFieldHint.concrete_remainder.1
    (keyFromPad pad) hint).val : Word)

/-- One 254-bit ciphertext, one public hint bit, and one unused high bit. -/
def pack (ciphertext : Ciphertext) (hint : Bool) : WordBytes :=
  PackedBits.encode fun byte bit =>
    if h : 8 * byte.val + bit.val < HintPayload.tableWidth then
      ciphertext ⟨8 * byte.val + bit.val, h⟩
    else if 8 * byte.val + bit.val = 254 then hint else false

def unpackHint (row : WordBytes) : Bool := PackedBits.decode row 31 6

def unpackCiphertext (row : WordBytes) (position : RowIndex) : Bool :=
  PackedBits.decode row
    ⟨position.val / 8, by have h : position.val < 254 := position.isLt; omega⟩
    ⟨position.val % 8, Nat.mod_lt _ (by decide)⟩

@[simp] theorem unpackHint_pack (ciphertext : Ciphertext) (hint : Bool) :
    unpackHint (pack ciphertext hint) = hint := by
  simp [unpackHint, pack, HintPayload.tableWidth]

@[simp] theorem unpackCiphertext_pack (ciphertext : Ciphertext) (hint : Bool) :
    unpackCiphertext (pack ciphertext hint) = ciphertext := by
  funext position
  have heq : 8 * (position.val / 8) + position.val % 8 = position.val := by omega
  unfold unpackCiphertext pack
  rw [PackedBits.decode_encode]
  simp only [heq, position.isLt, ↓reduceDIte]

def rowMask (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (coins : RowIndex → Coin) (index : RowIndex) : Word :=
  maskFromPad (pairs index false purpose) (padHint (pairs index false purpose) (coins index))

def row (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (params : Params) (coins : RowIndex → Coin) (index : RowIndex) : WordBytes :=
  pack
    (HintPayload.encrypt
      (HintPayload.encodeWord (HintPayload.share params
        (rowMask purpose pairs coins index) index true))
      (pairs index true purpose))
    (padHint (pairs index false purpose) (coins index))

/-- The leading word makes the independently sampled row masks sum to the
desired constant.  It is the only additional field element in a table. -/
def garble (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (params : Params) (coins : RowIndex → Coin) : Table :=
  let constant := HintPayload.encodeWord
    (params.constant - ∑ i, rowMask purpose pairs coins i)
  Table.ofWords (prependWord constant (row purpose pairs params coins))

@[simp] theorem garble_first (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (params : Params) (coins : RowIndex → Coin) :
    (garble purpose pairs params coins).words ⟨0, by decide⟩ =
      HintPayload.encodeWord (params.constant - ∑ i, rowMask purpose pairs coins i) := by
  unfold garble
  rw [Table.words_ofWords_apply]
  rw [prependWord_eq_cases]
  rfl

def openShare (purpose : Purpose) (table : Table) (bits : RowIndex → Bool)
    (labels : RowIndex → PadFamily) (index : RowIndex) : Option Word :=
  if bits index then
    HintPayload.openCiphertext (unpackCiphertext (table.words index.succ))
      (labels index purpose)
  else some (maskFromPad (labels index purpose) (unpackHint (table.words index.succ)))

def evaluateList (purpose : Purpose) (table : Table) (bits : RowIndex → Bool)
    (labels : RowIndex → PadFamily) : List RowIndex → Option Word
  | [] => some 0
  | index :: tail => do
      let value ← openShare purpose table bits labels index
      let rest ← evaluateList purpose table bits labels tail
      pure (value + rest)

def evaluate (purpose : Purpose) (table : Table) (bits : RowIndex → Bool)
    (labels : RowIndex → PadFamily) : Option Word := do
  let constant ← HintPayload.decodeWord (table.words ⟨0, by decide⟩)
  let value ← evaluateList purpose table bits labels (List.finRange HintPayload.tableWidth)
  pure (constant + value)

theorem openShare_garble (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (params : Params) (coins : RowIndex → Coin) (bits : RowIndex → Bool)
    (index : RowIndex) :
    openShare purpose (garble purpose pairs params coins) bits
        (fun i => pairs i (bits i)) index =
      some (HintPayload.share params (rowMask purpose pairs coins index) index (bits index)) := by
  have hrow : (garble purpose pairs params coins).words index.succ =
      row purpose pairs params coins index := by
    unfold garble
    rw [Table.words_ofWords_apply]
    simp only [prependWord_eq_cases, Fin.cases_succ]
  cases hb : bits index <;>
    simp [openShare, hrow, row, hb, HintPayload.share, HintPayload.bitWord, rowMask]

theorem evaluateList_garble (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (params : Params) (coins : RowIndex → Coin) (bits : RowIndex → Bool)
    (indices : List RowIndex) :
    evaluateList purpose (garble purpose pairs params coins) bits
        (fun i => pairs i (bits i)) indices =
      some (indices.foldr (fun index rest =>
        HintPayload.share params (rowMask purpose pairs coins index) index (bits index) + rest) 0) := by
  induction indices with
  | nil => rfl
  | cons index tail ih =>
      rw [evaluateList, openShare_garble, ih]
      rfl

private theorem foldr_finRange_eq_sum {width : Nat} (values : Fin width → Word) :
    (List.finRange width).foldr (fun index rest => values index + rest) 0 = ∑ i, values i := by
  induction width with
  | zero => simp
  | succ width ih =>
      rw [List.finRange_succ, List.foldr_cons, List.foldr_map, Fin.sum_univ_succ]
      exact congrArg (values 0 + ·) (ih (values := fun index => values index.succ))

theorem evaluate_garble (purpose : Purpose) (pairs : RowIndex → Bool → PadFamily)
    (params : Params) (coins : RowIndex → Coin) (bits : RowIndex → Bool) :
    evaluate purpose (garble purpose pairs params coins) bits (fun i => pairs i (bits i)) =
      some (params.coefficient * HintPayload.decodeBits bits + params.constant) := by
  unfold evaluate
  rw [evaluateList_garble]
  rw [garble_first, HintPayload.decodeWord_encodeWord]
  apply congrArg some
  rw [foldr_finRange_eq_sum]
  simp only [HintPayload.share_eq_weight, Finset.sum_add_distrib]
  unfold HintPayload.decodeBits
  rw [Finset.mul_sum]
  have heq : (∑ i, HintPayload.weight i * params.coefficient * HintPayload.bitWord (bits i)) =
      ∑ i, params.coefficient * (HintPayload.weight i * HintPayload.bitWord (bits i)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  ring

def wordCodec : FixedCodec WordBytes 32 where
  encode := id
  decode := .ok
  decode_encode := by intro; rfl
  encode_decode := by intro bytes value h; exact (Except.ok.inj h).symm

def Table.encode (table : Table) : ByteArray :=
  FixedCodec.encodeFin wordCodec tableWordCount table.words

def Table.decode (input : ByteArray) : Except WireDecodeError Table := do
  let words ← FixedCodec.decodeFin wordCodec tableWordCount input
  pure (Table.ofWords words)

@[simp] theorem Table.encode_size (table : Table) : table.encode.size = tableByteCount := by
  rw [Table.encode, FixedCodec.encodeFin_size]
  rfl

@[simp] theorem Table.decode_encode (table : Table) : Table.decode table.encode = .ok table := by
  unfold Table.decode Table.encode
  rw [FixedCodec.decodeFin_encode]
  simp

theorem Table.encode_decode {bytes : ByteArray} {table : Table}
    (h : Table.decode bytes = .ok table) : table.encode = bytes := by
  unfold Table.decode at h
  cases hwords : FixedCodec.decodeFin wordCodec tableWordCount bytes with
  | error error => simp [hwords, Except.bind, bind] at h
  | ok words =>
      have htable : (Table.ofWords words) = table := by
        simp only [hwords, Except.bind, bind] at h
        change Except.ok (Table.ofWords words) = Except.ok table at h
        exact Except.ok.inj h
      rw [← htable]
      simpa only [Table.encode, Table.words_ofWords] using
        FixedCodec.encodeFin_decode wordCodec hwords

theorem tableByteCount_eq : tableByteCount = 8160 := by decide
theorem familyByteCount_eq : 91 * 11 * tableByteCount = 8168160 := by decide
theorem familyByteCount_below_goal : 91 * 11 * tableByteCount < 8200000 := by decide


end G1Release.Submission.HintAffineTable
