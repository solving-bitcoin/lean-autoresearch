import GarblingPrize.Submission.BinaryFieldHint

namespace GarblingPrize.Submission.HintAffineTable

open GarblingPrize.Protected
open scoped BigOperators

abbrev Word := IdealAffineTable.Word
abbrev WordBytes := IdealAffineTable.WordBytes
abbrev Params := IdealAffineTable.Params
abbrev Ciphertext := IdealAffineTable.Ciphertext
abbrev Coin := Fin (4 * BinaryFieldHint.modulus)
abbrev RowIndex := Fin IdealAffineTable.tableWidth

abbrev tableWordCount : Nat := IdealAffineTable.tableWidth + 1
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
    have hi : index.val < IdealAffineTable.tableWidth + 1 := index.isLt
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
    ⟨Codec.decodeNatLE pad % BinaryFieldHint.binaryRange, by
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
    if h : 8 * byte.val + bit.val < IdealAffineTable.tableWidth then
      ciphertext ⟨8 * byte.val + bit.val, h⟩
    else if 8 * byte.val + bit.val = 254 then hint else false

def unpackHint (row : WordBytes) : Bool := PackedBits.decode row 31 6

def unpackCiphertext (row : WordBytes) (position : RowIndex) : Bool :=
  PackedBits.decode row
    ⟨position.val / 8, by have := position.isLt; norm_num [IdealAffineTable.tableWidth] at this; omega⟩
    ⟨position.val % 8, Nat.mod_lt _ (by decide)⟩

@[simp] theorem unpackHint_pack (ciphertext : Ciphertext) (hint : Bool) :
    unpackHint (pack ciphertext hint) = hint := by
  simp [unpackHint, pack, IdealAffineTable.tableWidth]

@[simp] theorem unpackCiphertext_pack (ciphertext : Ciphertext) (hint : Bool) :
    unpackCiphertext (pack ciphertext hint) = ciphertext := by
  funext position
  have heq : 8 * (position.val / 8) + position.val % 8 = position.val := by omega
  unfold unpackCiphertext pack
  rw [PackedBits.decode_encode]
  simp only [heq, position.isLt, ↓reduceDIte]

def rowMask (purpose : Purpose) (pairs : RowIndex → Bool → Label)
    (coins : RowIndex → Coin) (index : RowIndex) : Word :=
  maskFromPad (pairs index false purpose) (padHint (pairs index false purpose) (coins index))

def row (purpose : Purpose) (pairs : RowIndex → Bool → Label)
    (params : Params) (coins : RowIndex → Coin) (index : RowIndex) : WordBytes :=
  pack
    (IdealAffineTable.encrypt
      (IdealAffineTable.encodeWord (IdealAffineTable.share params
        (rowMask purpose pairs coins index) index true))
      (pairs index true purpose))
    (padHint (pairs index false purpose) (coins index))

/-- The leading word makes the independently sampled row masks sum to the
desired constant.  It is the only additional field element in a table. -/
def garble (purpose : Purpose) (pairs : RowIndex → Bool → Label)
    (params : Params) (coins : RowIndex → Coin) : Table :=
  let constant := IdealAffineTable.encodeWord
    (params.constant - ∑ i, rowMask purpose pairs coins i)
  Table.ofWords (prependWord constant (row purpose pairs params coins))

@[simp] theorem garble_first (purpose : Purpose) (pairs : RowIndex → Bool → Label)
    (params : Params) (coins : RowIndex → Coin) :
    (garble purpose pairs params coins).words ⟨0, by decide⟩ =
      IdealAffineTable.encodeWord (params.constant - ∑ i, rowMask purpose pairs coins i) := by
  unfold garble
  rw [Table.words_ofWords_apply]
  rw [prependWord_eq_cases]
  rfl

def openShare (purpose : Purpose) (table : Table) (bits : RowIndex → Bool)
    (labels : RowIndex → Label) (index : RowIndex) : Option Word :=
  if bits index then
    IdealAffineTable.openCiphertext (unpackCiphertext (table.words index.succ))
      (labels index purpose)
  else some (maskFromPad (labels index purpose) (unpackHint (table.words index.succ)))

def evaluateList (purpose : Purpose) (table : Table) (bits : RowIndex → Bool)
    (labels : RowIndex → Label) : List RowIndex → Option Word
  | [] => some 0
  | index :: tail => do
      let value ← openShare purpose table bits labels index
      let rest ← evaluateList purpose table bits labels tail
      pure (value + rest)

def evaluate (purpose : Purpose) (table : Table) (bits : RowIndex → Bool)
    (labels : RowIndex → Label) : Option Word := do
  let constant ← IdealAffineTable.decodeWord (table.words ⟨0, by decide⟩)
  let value ← evaluateList purpose table bits labels (List.finRange IdealAffineTable.tableWidth)
  pure (constant + value)

theorem openShare_garble (purpose : Purpose) (pairs : RowIndex → Bool → Label)
    (params : Params) (coins : RowIndex → Coin) (bits : RowIndex → Bool)
    (index : RowIndex) :
    openShare purpose (garble purpose pairs params coins) bits
        (fun i => pairs i (bits i)) index =
      some (IdealAffineTable.share params (rowMask purpose pairs coins index) index (bits index)) := by
  have hrow : (garble purpose pairs params coins).words index.succ =
      row purpose pairs params coins index := by
    unfold garble
    rw [Table.words_ofWords_apply]
    simp only [prependWord_eq_cases, Fin.cases_succ]
  cases hb : bits index <;>
    simp [openShare, hrow, row, hb, IdealAffineTable.share, rowMask]

theorem evaluateList_garble (purpose : Purpose) (pairs : RowIndex → Bool → Label)
    (params : Params) (coins : RowIndex → Coin) (bits : RowIndex → Bool)
    (indices : List RowIndex) :
    evaluateList purpose (garble purpose pairs params coins) bits
        (fun i => pairs i (bits i)) indices =
      some (indices.foldr (fun index rest =>
        IdealAffineTable.share params (rowMask purpose pairs coins index) index (bits index) + rest) 0) := by
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

theorem evaluate_garble (purpose : Purpose) (pairs : RowIndex → Bool → Label)
    (params : Params) (coins : RowIndex → Coin) (bits : RowIndex → Bool) :
    evaluate purpose (garble purpose pairs params coins) bits (fun i => pairs i (bits i)) =
      some (params.coefficient * IdealAffineTable.decodeBits bits + params.constant) := by
  unfold evaluate
  rw [evaluateList_garble]
  rw [garble_first, IdealAffineTable.decodeWord_encodeWord]
  apply congrArg some
  rw [foldr_finRange_eq_sum]
  simp only [IdealAffineTable.share_eq_weight, Finset.sum_add_distrib]
  unfold IdealAffineTable.decodeBits
  rw [Finset.mul_sum]
  have heq : (∑ i, IdealAffineTable.weight i * params.coefficient * IdealAffineTable.bitWord (bits i)) =
      ∑ i, params.coefficient * (IdealAffineTable.weight i * IdealAffineTable.bitWord (bits i)) := by
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

/-! A limit of further row-format compression.

Fix both label pads and all private coins of a row. If subtracting its two
decoded branches recovers an arbitrary field difference, the serialized row
must distinguish every field element. Thus even an optimally packed row
needs at least 254 bits. This is a bound on independent row-difference
encodings, not on all garbling schemes: changing the algebraic encoding or
coupling rows can fall outside its hypothesis.

At the current 91 * 11 * 254 rows, this already forces 8,072,565 bytes before
any table headers. Consequently the 4.1 MB goal requires changing more than
the bit packing of the present row construction.
-/

theorem rowEncoding_injective {C : Type*} (encode : Word → C)
    (difference : C → Word) (hdecode : ∀ value, difference (encode value) = value) :
    Function.Injective encode := by
  intro left right hequal
  rw [← hdecode left, ← hdecode right, hequal]

/-- With both fixed pads available, the row difference recovers the slope.
This auxiliary decoder is used only for the counting argument. -/
def coefficientFromRow (falsePad truePad : WordBytes) (index : RowIndex)
    (bytes : WordBytes) : Word :=
  ((IdealAffineTable.openCiphertext (unpackCiphertext bytes) truePad).getD 0 -
    maskFromPad falsePad (unpackHint bytes)) / IdealAffineTable.weight index

theorem coefficientFromRow_row (purpose : Purpose) (pairs : RowIndex → Bool → Label)
    (params : Params) (coins : RowIndex → Coin) (index : RowIndex) :
    coefficientFromRow (pairs index false purpose) (pairs index true purpose) index
      (row purpose pairs params coins index) = params.coefficient := by
  have htwo : (2 : Word) ≠ 0 := by decide
  have hweight : IdealAffineTable.weight index ≠ 0 := by
    rw [IdealAffineTable.weight_eq_pow]
    exact pow_ne_zero _ htwo
  simp only [coefficientFromRow, row, unpackCiphertext_pack,
    IdealAffineTable.openCiphertext_encrypt, Option.getD_some,
    unpackHint_pack, IdealAffineTable.share_eq_weight,
    IdealAffineTable.bitWord, ↓reduceIte, mul_one, rowMask, add_sub_cancel_right]
  exact mul_div_cancel_left₀ _ hweight

theorem rowEncoding_bits_ge (bits : Nat) (encode : Word → (Fin bits → Bool))
    (difference : (Fin bits → Bool) → Word)
    (hdecode : ∀ value, difference (encode value) = value) : 254 ≤ bits := by
  have hcard := Fintype.card_le_of_injective encode
    (rowEncoding_injective encode difference hdecode)
  have hsize : baseFieldModulus ≤ 2 ^ bits := by
    simpa [Word, IdealAffineTable.Word, BN254.Fq] using hcard
  have hfield : 2 ^ 253 < baseFieldModulus := by
    norm_num [baseFieldModulus]
  by_contra hbits
  have hpower : 2 ^ bits ≤ 2 ^ 253 := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem independentRows_byte_floor (bits bytes : Nat)
    (encode : Word → (Fin bits → Bool))
    (difference : (Fin bits → Bool) → Word)
    (hdecode : ∀ value, difference (encode value) = value)
    (hstorage : 91 * 11 * 254 * bits ≤ 8 * bytes) : 8072565 ≤ bytes := by
  have := rowEncoding_bits_ge bits encode difference hdecode
  omega

theorem losslessRowCompression_bits_ge (bits : Nat)
    (purpose : Purpose) (pairs : RowIndex → Bool → Label)
    (coins : RowIndex → Coin) (index : RowIndex)
    (compress : WordBytes → (Fin bits → Bool))
    (expand : (Fin bits → Bool) → WordBytes)
    (hlossless : ∀ coefficient : Word,
      expand (compress (row purpose pairs ⟨coefficient, 0⟩ coins index)) =
        row purpose pairs ⟨coefficient, 0⟩ coins index) : 254 ≤ bits := by
  apply rowEncoding_bits_ge bits
    (fun coefficient => compress (row purpose pairs ⟨coefficient, 0⟩ coins index))
    (fun encoded => coefficientFromRow (pairs index false purpose)
      (pairs index true purpose) index (expand encoded))
  intro coefficient
  rw [hlossless, coefficientFromRow_row]

theorem fiveTable_budget : 91 * 5 * tableByteCount = 3712800 := by decide
theorem fiveTable_below_new_goal : 91 * 5 * tableByteCount < 4100000 := by decide
theorem sixTable_above_new_goal : 4100000 < 91 * 6 * tableByteCount := by decide

end GarblingPrize.Submission.HintAffineTable
