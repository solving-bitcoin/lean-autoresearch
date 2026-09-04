import GarblingPrize.Protected.Target

namespace GarblingPrize.Submission

open GarblingPrize.Protected

/-!
# Fixed-width composable codecs

`FixedCodec` packages one canonical fixed-width byte encoding.  The generic
`Fin` combinators below serialize and parse fixed-size families while proving
the exact two codec laws required by the protected challenge boundary.
-/

/-- A fixed-width canonical codec with both round-trip directions. -/
structure FixedCodec (α : Type) (width : Nat) where
  encode : α → Bytes width
  decode : Bytes width → Except WireDecodeError α
  decode_encode : ∀ value, decode (encode value) = .ok value
  encode_decode : ∀ {bytes value}, decode bytes = .ok value → encode value = bytes

namespace FixedCodec

/-- Consume exactly `count` leading bytes and retain the unconsumed suffix. -/
def takeSection (count : Nat) (input : ByteArray) :
    Except WireDecodeError (Bytes count × ByteArray) :=
  if _henough : count ≤ input.size then
    let leading := input.extract 0 count
    let suffix := input.extract count input.size
    match Bytes.ofByteArray? count leading with
    | some fixed => .ok (fixed, suffix)
    | none => .error .invalidLength
  else
    .error .unexpectedEnd

theorem takeSection_complete {input : ByteArray} {fixed : Bytes count}
    {rest : ByteArray} (h : takeSection count input = .ok (fixed, rest)) :
    fixed.toByteArray ++ rest = input := by
  unfold takeSection at h
  split at h
  · rename_i henough
    dsimp only at h
    split at h
    · rename_i candidate hcand
      cases h
      rw [← (Bytes.ofByteArray?_eq_some_iff.mp hcand)]
      rw [ByteArray.extract_append_extract]
      simp
    · simp at h
  · simp at h

@[simp] theorem takeSection_fixed_append (left : Bytes count)
    (right : ByteArray) :
    takeSection count (left.toByteArray ++ right) = .ok (left, right) := by
  have hleading :
      (left.toByteArray ++ right).extract 0 count = left.toByteArray :=
    ByteArray.extract_append_eq_left (by simp)
  have hsuffix :
      (left.toByteArray ++ right).extract count
          (left.toByteArray ++ right).size = right :=
    ByteArray.extract_append_eq_right (by simp) (by simp)
  unfold takeSection
  split
  · rw [hleading, hsuffix]
    dsimp only
    rw [Bytes.ofByteArray?_toByteArray]
  · rename_i hnotEnough
    exact False.elim (hnotEnough (by simp))

/-- Specification encoder for a fixed-size family.  Its right-associated
appends are convenient for proofs, but quadratic when executed on a large
family because every step prepends to the already-materialized suffix. -/
private def encodeFinSpec (codec : FixedCodec α width) :
    (count : Nat) → (Fin count → α) → ByteArray
  | 0, _ => ByteArray.empty
  | count + 1, values =>
      (codec.encode (values 0)).toByteArray ++
        encodeFinSpec codec count (fun index => values index.succ)

/-- Executable encoder with direct indexing.  `Fin.foldl` carries the numeric
index through its tail-recursive loop, so element `i` is obtained as `values i`
instead of crossing `i` nested `fun j => values j.succ` closures.  Together
with the uniquely owned byte accumulator, this makes both family traversal and
serialization linear. -/
private def encodeFinAcc (codec : FixedCodec α width) (count : Nat)
    (values : Fin count → α) (output : ByteArray) : ByteArray :=
  Fin.foldl count
    (fun output index =>
      output ++ (codec.encode (values index)).toByteArray)
    output

/-- Concatenate the canonical encodings of a fixed-size family. -/
def encodeFin (codec : FixedCodec α width) (count : Nat)
    (values : Fin count → α) : ByteArray :=
  encodeFinAcc codec count values ByteArray.empty

/-- Encode independent fixed-width values concurrently, then concatenate them
in canonical index order. `Task.spawn` has a transparent pure specification,
so this optimization has exactly the same logical result as `encodeFin`; only
compiled execution uses the runtime worker pool. -/
def encodeFinParallel (codec : FixedCodec α width) (count : Nat)
    (values : Fin count → α) : ByteArray :=
  let tasks : Vector (Task (Bytes width)) count :=
    Vector.ofFn fun index => Task.spawn fun _ => codec.encode (values index)
  Fin.foldl count
    (fun output index => output ++ tasks[index.val].get.toByteArray)
    ByteArray.empty

@[simp] theorem encodeFinParallel_eq (codec : FixedCodec α width)
    (values : Fin count → α) :
    encodeFinParallel codec count values = encodeFin codec count values := by
  unfold encodeFinParallel encodeFin encodeFinAcc
  simp [Task.spawn]

private theorem encodeFinAcc_eq (codec : FixedCodec α width)
    (values : Fin count → α) (output : ByteArray) :
    encodeFinAcc codec count values output =
      output ++ encodeFinSpec codec count values := by
  induction count generalizing output with
  | zero => simp [encodeFinAcc, encodeFinSpec]
  | succ count ih =>
      rw [encodeFinAcc, Fin.foldl_succ]
      change encodeFinAcc codec count (fun index => values index.succ)
          (output ++ (codec.encode (values 0)).toByteArray) = _
      rw [ih, encodeFinSpec, ByteArray.append_assoc]

private theorem encodeFin_eq_spec (codec : FixedCodec α width)
    (values : Fin count → α) :
    encodeFin codec count values = encodeFinSpec codec count values := by
  simp [encodeFin, encodeFinAcc_eq]

/-- Parse a fixed-size family and return the remaining byte suffix. -/
def decodeFinPrefix (codec : FixedCodec α width) :
    (count : Nat) → ByteArray →
      Except WireDecodeError ((Fin count → α) × ByteArray)
  | 0, input => .ok (Fin.elim0, input)
  | count + 1, input => do
      let (headBytes, input) ← takeSection width input
      let head ← codec.decode headBytes
      let (tail, rest) ← decodeFinPrefix codec count input
      .ok (Fin.cases head tail, rest)

private theorem finCases_eta (values : Fin (count + 1) → α) :
    Fin.cases (values 0) (fun index => values index.succ) = values := by
  funext index
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

@[simp] theorem encodeFin_size (codec : FixedCodec α width)
    (values : Fin count → α) :
    (encodeFin codec count values).size = count * width := by
  rw [encodeFin_eq_spec]
  induction count with
  | zero => simp [encodeFinSpec]
  | succ count ih =>
      rw [encodeFinSpec, ByteArray.size_append, Bytes.size_toByteArray, ih]
      simp [Nat.succ_mul, Nat.add_comm]

private theorem decodeFinPrefix_encodeSpec_append
    (codec : FixedCodec α width)
    (values : Fin count → α) (rest : ByteArray) :
    decodeFinPrefix codec count (encodeFinSpec codec count values ++ rest) =
      .ok (values, rest) := by
  induction count with
  | zero =>
      have hvalues : (Fin.elim0 : Fin 0 → α) = values := by
        funext index
        exact index.elim0
      simp [encodeFinSpec, decodeFinPrefix, hvalues]
  | succ count ih =>
      simp only [encodeFinSpec, decodeFinPrefix, ByteArray.append_assoc]
      rw [takeSection_fixed_append]
      simp only [Except.bind, bind]
      rw [codec.decode_encode]
      rw [ih]
      change Except.ok (Fin.cases (values 0) (fun index => values index.succ), rest) =
        Except.ok (values, rest)
      rw [finCases_eta]

@[simp] theorem decodeFinPrefix_encode_append (codec : FixedCodec α width)
    (values : Fin count → α) (rest : ByteArray) :
    decodeFinPrefix codec count (encodeFin codec count values ++ rest) =
      .ok (values, rest) := by
  rw [encodeFin_eq_spec]
  exact decodeFinPrefix_encodeSpec_append codec values rest

private theorem decodeFinPrefix_complete_spec (codec : FixedCodec α width)
    {input : ByteArray} {values : Fin count → α} {rest : ByteArray}
    (h : decodeFinPrefix codec count input = .ok (values, rest)) :
    encodeFinSpec codec count values ++ rest = input := by
  induction count generalizing input rest with
  | zero =>
      simp only [decodeFinPrefix, Except.ok.injEq, Prod.mk.injEq] at h
      rcases h with ⟨hvalues, hrest⟩
      subst rest
      have hempty : values = Fin.elim0 := by
        funext index
        exact index.elim0
      subst values
      rfl
  | succ count ih =>
      unfold decodeFinPrefix at h
      cases hsection : takeSection width input with
      | error error => simp [hsection, Except.bind, bind] at h
      | ok parsedSection =>
          rcases parsedSection with ⟨headBytes, tailInput⟩
          cases hhead : codec.decode headBytes with
          | error error => simp [hsection, hhead, Except.bind, bind] at h
          | ok head =>
              cases htail : decodeFinPrefix codec count tailInput with
              | error error =>
                  simp [hsection, hhead, htail, Except.bind, bind] at h
              | ok decoded =>
                  rcases decoded with ⟨tail, decodedRest⟩
                  simp [hsection, hhead, htail, Except.bind, bind] at h
                  rcases h with ⟨hvalues, hrest⟩
                  rw [← hvalues, ← hrest, encodeFinSpec]
                  simp only [Fin.cases_zero, Fin.cases_succ]
                  rw [ByteArray.append_assoc, ih htail,
                    codec.encode_decode hhead, takeSection_complete hsection]

theorem decodeFinPrefix_complete (codec : FixedCodec α width)
    {input : ByteArray} {values : Fin count → α} {rest : ByteArray}
    (h : decodeFinPrefix codec count input = .ok (values, rest)) :
    encodeFin codec count values ++ rest = input := by
  rw [encodeFin_eq_spec]
  exact decodeFinPrefix_complete_spec codec h

/-- Repack the recursively decoded family into an array-backed function.
Without this step, repeated `Fin.cases` lookups are linear in the index and a
full table evaluation becomes quadratic in the table width. -/
private def packFunction (values : Fin count → α) : Fin count → α :=
  let packed := Array.ofFn values
  fun index => packed[index.val]'(by simpa [packed] using index.isLt)

@[simp] private theorem packFunction_eq (values : Fin count → α) :
    packFunction values = values := by
  funext index
  simp [packFunction]

/-- Proof specification for exact decoding. -/
private def decodeFinSpec (codec : FixedCodec α width) (count : Nat)
    (input : ByteArray) :
    Except WireDecodeError (Fin count → α) := do
  let (values, rest) ← decodeFinPrefix codec count input
  if rest.size = 0 then .ok (packFunction values) else .error .trailingBytes

/-- Proof specification for the list-accumulating parser.  Its shrinking
`ByteArray` argument is convenient for the structural proof below, but must
not be used as the executable implementation: materializing every remaining
suffix makes nested artifact decoding quadratic in the wire size. -/
private def decodeFinListPrefixSpec (codec : FixedCodec α width) :
    (count : Nat) → ByteArray → List α →
      Except WireDecodeError (List α × ByteArray)
  | 0, input, reversed => .ok (reversed.reverse, input)
  | count + 1, input, reversed => do
      let (headBytes, input) ← takeSection width input
      let head ← codec.decode headBytes
      decodeFinListPrefixSpec codec count input (head :: reversed)

private theorem decodeFinListPrefixSpec_eq (codec : FixedCodec α width)
    (input : ByteArray) (reversed : List α) :
    decodeFinListPrefixSpec codec count input reversed =
      match decodeFinPrefix codec count input with
      | .error error => .error error
      | .ok (values, rest) =>
          .ok (reversed.reverse ++ List.ofFn values, rest) := by
  induction count generalizing input reversed with
  | zero => simp [decodeFinListPrefixSpec, decodeFinPrefix]
  | succ count ih =>
      unfold decodeFinListPrefixSpec decodeFinPrefix
      cases hsection : takeSection width input with
      | error error => simp [hsection, Except.bind, bind]
      | ok parsedSection =>
          rcases parsedSection with ⟨headBytes, tailInput⟩
          simp only [hsection, Except.bind, bind]
          cases hhead : codec.decode headBytes with
          | error error => simp [hhead]
          | ok head =>
              simp only [hhead]
              rw [show decodeFinListPrefixSpec codec count tailInput
                  (head :: reversed) =
                    match decodeFinPrefix codec count tailInput with
                    | .error error => .error error
                    | .ok (values, rest) =>
                        .ok ((head :: reversed).reverse ++ List.ofFn values,
                          rest) from ih tailInput (head :: reversed)]
              cases htail : decodeFinPrefix codec count tailInput with
              | error error => simp [htail]
              | ok tail =>
                  rcases tail with ⟨values, rest⟩
                  simp only [Except.pure, List.reverse_cons, List.ofFn_succ,
                    Fin.cases_zero, Fin.cases_succ]
                  rw [List.append_assoc]
                  have heta : (fun i => values i) = values := rfl
                  rw [heta]
                  simp only [List.singleton_append]

/-- Splitting the suffix at `position` agrees with splitting the original
array at that absolute cursor.  This is the bridge that lets the executable
parser use one shared input while retaining the suffix-based proof model. -/
private theorem takeSection_extract (input : ByteArray)
    (position count : Nat) (hposition : position ≤ input.size) :
    takeSection count (input.extract position input.size) =
      if _henough : position + count ≤ input.size then
        let leading := input.extract position (position + count)
        let suffix := input.extract (position + count) input.size
        match Bytes.ofByteArray? count leading with
        | some fixed => .ok (fixed, suffix)
        | none => .error .invalidLength
      else
        .error .unexpectedEnd := by
  unfold takeSection
  simp only [ByteArray.size_extract, Nat.min_self]
  by_cases henough : position + count ≤ input.size
  · have hcount : count ≤ input.size - position := by omega
    simp only [hcount, henough, dite_true]
    rw [ByteArray.extract_extract, ByteArray.extract_extract]
    simp only [Nat.min_eq_left henough, Nat.add_sub_of_le hposition,
      Nat.min_self, Nat.add_zero]
  · have hcount : ¬ count ≤ input.size - position := by omega
    simp only [hcount, henough, dite_false]

/-- Cursor parser over one shared input.  Each step copies only its fixed-width
section; it never copies the shrinking multi-megabyte remainder. -/
private def decodeFinListAt (codec : FixedCodec α width) :
    (count position : Nat) → ByteArray → List α →
      Except WireDecodeError (List α × ByteArray)
  | 0, position, input, reversed =>
      .ok (reversed.reverse, input.extract position input.size)
  | count + 1, position, input, reversed =>
      if _henough : position + width ≤ input.size then
        let leading := input.extract position (position + width)
        match Bytes.ofByteArray? width leading with
        | none => .error .invalidLength
        | some headBytes => do
            let head ← codec.decode headBytes
            decodeFinListAt codec count (position + width) input
              (head :: reversed)
      else
        .error .unexpectedEnd

private theorem decodeFinListAt_eq (codec : FixedCodec α width)
    (input : ByteArray) (position : Nat) (reversed : List α)
    (hposition : position ≤ input.size) :
    decodeFinListAt codec count position input reversed =
      decodeFinListPrefixSpec codec count
        (input.extract position input.size) reversed := by
  induction count generalizing position reversed with
  | zero => rfl
  | succ count ih =>
      unfold decodeFinListAt decodeFinListPrefixSpec
      rw [takeSection_extract input position width hposition]
      by_cases henough : position + width ≤ input.size
      · simp only [henough, dite_true]
        cases hfixed : Bytes.ofByteArray? width
            (input.extract position (position + width)) with
        | none => simp [Except.bind, bind]
        | some headBytes =>
            simp only [Except.bind, bind]
            cases hhead : codec.decode headBytes with
            | error error => simp
            | ok head =>
                simp only
                exact ih (position + width) (head :: reversed) henough
      · simp only [henough, dite_false]
        rfl

/-- Tail-recursive exact parser with linear byte movement. -/
private def decodeFinListPrefix (codec : FixedCodec α width)
    (count : Nat) (input : ByteArray) (reversed : List α) :
    Except WireDecodeError (List α × ByteArray) :=
  decodeFinListAt codec count 0 input reversed

private theorem decodeFinListPrefix_eq (codec : FixedCodec α width)
    (input : ByteArray) (reversed : List α) :
    decodeFinListPrefix codec count input reversed =
      match decodeFinPrefix codec count input with
      | .error error => .error error
      | .ok (values, rest) =>
          .ok (reversed.reverse ++ List.ofFn values, rest) := by
  unfold decodeFinListPrefix
  rw [decodeFinListAt_eq codec input 0 reversed (by omega)]
  simpa using decodeFinListPrefixSpec_eq
    (codec := codec) (count := count) input reversed

private def listFunction (values : List α) (h : values.length = count) :
    Fin count → α :=
  let packed := values.toArray
  fun index => packed[index.val]'(by simpa [packed, h] using index.isLt)

@[simp] private theorem listFunction_ofFn (values : Fin count → α) :
    listFunction (List.ofFn values) (by simp) = values := by
  funext index
  simp [listFunction]

/-- Decode exactly `count` values, rejecting every trailing byte.  The parser
accumulates a list, reverses it once, and exposes an array-backed function. -/
def decodeFin (codec : FixedCodec α width) (count : Nat) (input : ByteArray) :
    Except WireDecodeError (Fin count → α) := do
  let (values, rest) ← decodeFinListPrefix codec count input []
  if rest.size = 0 then
    if hlength : values.length = count then
      .ok (listFunction values hlength)
    else
      .error .invalidLength
  else
    .error .trailingBytes

private theorem decodeFin_eq_spec (codec : FixedCodec α width)
    (count : Nat) (input : ByteArray) :
    decodeFin codec count input = decodeFinSpec codec count input := by
  unfold decodeFin decodeFinSpec
  rw [decodeFinListPrefix_eq]
  cases hprefix : decodeFinPrefix codec count input with
  | error error => simp [hprefix, Except.bind, bind]
  | ok decoded =>
      rcases decoded with ⟨values, rest⟩
      simp [hprefix, Except.bind, bind]

@[simp] theorem decodeFin_encode (codec : FixedCodec α width)
    (values : Fin count → α) :
    decodeFin codec count (encodeFin codec count values) = .ok values := by
  rw [decodeFin_eq_spec]
  unfold decodeFinSpec
  have hvalues : decodeFinPrefix codec count (encodeFin codec count values) =
      .ok (values, ByteArray.empty) := by
    simpa only [ByteArray.append_empty] using
      decodeFinPrefix_encode_append codec values ByteArray.empty
  rw [hvalues]
  simp [Except.bind, bind]

theorem encodeFin_decode (codec : FixedCodec α width) {input : ByteArray}
    {values : Fin count → α}
    (h : decodeFin codec count input = .ok values) :
    encodeFin codec count values = input := by
  rw [decodeFin_eq_spec] at h
  unfold decodeFinSpec at h
  cases hprefix : decodeFinPrefix codec count input with
  | error error => simp [hprefix, Except.bind, bind] at h
  | ok decoded =>
      rcases decoded with ⟨parsed, rest⟩
      simp [hprefix, Except.bind, bind] at h
      split at h
      · rename_i hrest
        have hparsed : parsed = values := by simpa using h
        have hcomplete := decodeFinPrefix_complete codec hprefix
        rw [hrest, ByteArray.append_empty] at hcomplete
        rw [← hparsed]
        exact hcomplete
      · simp at h

end FixedCodec

end GarblingPrize.Submission
