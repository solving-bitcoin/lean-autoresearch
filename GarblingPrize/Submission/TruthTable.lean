import GarblingPrize.Submission.IdealAffineTablePrivacy

namespace GarblingPrize.Submission.TruthTable

open GarblingPrize.Protected

abbrev Profile := BN254.bn254
abbrev Input := AffineInput Profile
abbrev Hidden := HiddenInput Profile
abbrev Output := BN254.CanonicalOutput
abbrev InputBits := BitIndex → Bool
abbrev RowIndex := InputBits
abbrev Block := Bytes 32
abbrev Row := Bytes 64

noncomputable section

def tableCount : Nat := 2 ^ coordinateBitCount
abbrev rowByteCount : Nat := 64
def artifactByteCount : Nat := tableCount * rowByteCount

theorem tableCount_eq : tableCount = 2 ^ coordinateBitCount := by
  rfl

def rowIndex (input : Input) : RowIndex := inputBit input

def rowBits (row : RowIndex) : InputBits := row

@[simp] theorem rowBits_rowIndex (input : Input) :
    rowBits (rowIndex input) = inputBit input := rfl

private theorem base_lt_two_pow_coordinateWidth :
    baseFieldModulus < 2 ^ coordinateWidth := by
  norm_num [baseFieldModulus, coordinateWidth]

private theorem xBits_inputBit (input : Input) (index : Fin coordinateWidth) :
    inputBit input ⟨index.val, by
      change index.val < 2 * coordinateWidth
      omega⟩ =
      input.x.val.testBit index.val := by
  simp [inputBit]

private theorem yBits_inputBit (input : Input) (index : Fin coordinateWidth) :
    inputBit input ⟨coordinateWidth + index.val, by
      change coordinateWidth + index.val < 2 * coordinateWidth
      omega⟩ =
      input.y.val.testBit index.val := by
  simp [inputBit]

theorem inputBit_injective : Function.Injective (@inputBit Profile) := by
  intro left right hequal
  have hxBits :
      (fun index : Fin coordinateWidth => left.x.val.testBit index.val) =
        fun index : Fin coordinateWidth => right.x.val.testBit index.val := by
    funext index
    rw [← xBits_inputBit left index, ← xBits_inputBit right index, hequal]
  have hyBits :
      (fun index : Fin coordinateWidth => left.y.val.testBit index.val) =
        fun index : Fin coordinateWidth => right.y.val.testBit index.val := by
    funext index
    rw [← yBits_inputBit left index, ← yBits_inputBit right index, hequal]
  have hxNat := congrArg Nat.ofBits hxBits
  have hyNat := congrArg Nat.ofBits hyBits
  rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt
      (Nat.lt_trans left.x.isLt base_lt_two_pow_coordinateWidth),
    Nat.ofBits_testBit, Nat.mod_eq_of_lt
      (Nat.lt_trans right.x.isLt base_lt_two_pow_coordinateWidth)] at hxNat
  rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt
      (Nat.lt_trans left.y.isLt base_lt_two_pow_coordinateWidth),
    Nat.ofBits_testBit, Nat.mod_eq_of_lt
      (Nat.lt_trans right.y.isLt base_lt_two_pow_coordinateWidth)] at hyNat
  cases left with
  | mk lx ly lh =>
      cases right with
      | mk rx ry rh =>
          simp only at hxNat hyNat
          have hx : lx = rx := Fin.ext hxNat
          have hy : ly = ry := Fin.ext hyNat
          subst rx
          subst ry
          rfl

theorem rowIndex_injective : Function.Injective rowIndex := by
  intro left right hequal
  apply inputBit_injective
  rw [← rowBits_rowIndex left, ← rowBits_rowIndex right, hequal]

noncomputable def inputForRow (row : RowIndex) : Option Input := by
  classical
  exact if h : ∃ input, rowIndex input = row then
    some (Classical.choose h)
  else
    none

theorem inputForRow_rowIndex (input : Input) :
    inputForRow (rowIndex input) = some input := by
  unfold inputForRow
  split
  · rename_i hexists
    congr 1
    apply rowIndex_injective
    exact Classical.choose_spec hexists
  · rename_i hnone
    exact False.elim (hnone ⟨input, rfl⟩)

def zeroBlock : Block := Bytes.zero 32

def encodeCanonical (value : CanonicalFq) : Block :=
  Codec.natLE 32 value.val

def decodeCanonical (bytes : Block) : Option CanonicalFq :=
  let value := Codec.decodeNatLE bytes
  if h : value < baseFieldModulus then some ⟨value, h⟩ else none

@[simp] theorem decodeCanonical_encodeCanonical (value : CanonicalFq) :
    decodeCanonical (encodeCanonical value) = some value := by
  unfold decodeCanonical encodeCanonical
  rw [Codec.decodeNatLE_natLE_of_lt 32 value.val
    (Nat.lt_trans value.isLt (by
      norm_num [baseFieldModulus]))]
  simp only [value.isLt, ↓reduceDIte]

private theorem encodeCanonical_zero :
    encodeCanonical (⟨0, by norm_num [baseFieldModulus]⟩ : CanonicalFq) =
      zeroBlock := by
  apply Vector.ext
  intro index hindex
  simp [encodeCanonical, zeroBlock, Bytes.zero, Codec.natLE,
    Bytes.ofFn]

@[simp] theorem decodeCanonical_zeroBlock :
    decodeCanonical zeroBlock = some ⟨0, by
      norm_num [baseFieldModulus]⟩ := by
  rw [← encodeCanonical_zero, decodeCanonical_encodeCanonical]

def encodeOutput : Output → Row
  | .infinity => Bytes.append zeroBlock zeroBlock
  | .affine x y _ => Bytes.append (encodeCanonical x) (encodeCanonical y)

def firstBlock (row : Row) : Block :=
  IdealAffineTable.rowHalf false row

def secondBlock (row : Row) : Block :=
  IdealAffineTable.rowHalf true row

@[simp] theorem firstBlock_append (left right : Block) :
    firstBlock (Bytes.append left right) = left := by
  apply Vector.ext
  intro index hindex
  simp [firstBlock, IdealAffineTable.rowHalf, Bytes.append, Bytes.ofFn,
    Vector.get_eq_getElem]

@[simp] theorem secondBlock_append (left right : Block) :
    secondBlock (Bytes.append left right) = right := by
  apply Vector.ext
  intro index hindex
  simp [secondBlock, IdealAffineTable.rowHalf, Bytes.append, Bytes.ofFn,
    Vector.get_eq_getElem]

noncomputable def decodeOutput (row : Row) : Option Output := by
  classical
  exact do
    let x ← decodeCanonical (firstBlock row)
    let y ← decodeCanonical (secondBlock row)
    if hzero : x.val = 0 ∧ y.val = 0 then
      some .infinity
    else if hcurve : BN254.OnCurve x y then
      some (.affine x y hcurve)
    else
      none

private theorem zero_pair_not_onCurve (x y : CanonicalFq)
    (hx : x.val = 0) (hy : y.val = 0) : ¬ BN254.OnCurve x y := by
  intro hcurve
  simp [BN254.OnCurve, hx, hy] at hcurve
  have hthree : (3 : BN254.Fq) ≠ 0 := by
    intro hzero
    have hdiv : baseFieldModulus ∣ 3 :=
      (ZMod.natCast_eq_zero_iff 3 baseFieldModulus).mp hzero
    norm_num [baseFieldModulus] at hdiv
  exact hthree hcurve.symm

@[simp] theorem decodeOutput_encodeOutput (output : Output) :
    decodeOutput (encodeOutput output) = some output := by
  classical
  cases output with
  | infinity =>
      simp [decodeOutput, encodeOutput]
  | affine x y hcurve =>
      have hnotZero : ¬ (x.val = 0 ∧ y.val = 0) := by
        intro hzero
        exact zero_pair_not_onCurve x y hzero.1 hzero.2 hcurve
      simp only [decodeOutput, encodeOutput, firstBlock_append,
        secondBlock_append, decodeCanonical_encodeCanonical]
      change (if hzero : x.val = 0 ∧ y.val = 0 then
          some BN254.CanonicalOutput.infinity
        else if hcurve' : BN254.OnCurve x y then
          some (BN254.CanonicalOutput.affine x y hcurve')
        else none) = some (BN254.CanonicalOutput.affine x y hcurve)
      rw [dif_neg hnotZero, dif_pos hcurve]

noncomputable def outputForRow (hidden : Hidden)
    (row : RowIndex) : Output :=
  match inputForRow row with
  | none => .infinity
  | some input => Profile.outputEquiv.symm (reference Profile hidden input)

theorem outputForRow_selected (hidden : Hidden) (input : Input) :
    outputForRow hidden (rowIndex input) =
      Profile.outputEquiv.symm (reference Profile hidden input) := by
  simp [outputForRow, inputForRow_rowIndex]
  rfl

def purpose (row : RowIndex) (chunk : Bool) : Purpose :=
  Nat.pair (Nat.ofBits row) (if chunk then 1 else 0)

theorem xor_comm (left right : Block) :
    Bytes.xor left right = Bytes.xor right left := by
  apply Vector.ext
  intro index hindex
  simp [Bytes.xor, Bytes.ofFn, Vector.get_eq_getElem, UInt8.xor_comm]

theorem xor_assoc (left middle right : Block) :
    Bytes.xor (Bytes.xor left middle) right =
      Bytes.xor left (Bytes.xor middle right) := by
  apply Vector.ext
  intro index hindex
  simp [Bytes.xor, Bytes.ofFn, Vector.get_eq_getElem, UInt8.xor_assoc]

instance : Std.Commutative (@Bytes.xor 32) := ⟨xor_comm⟩
instance : Std.Associative (@Bytes.xor 32) := ⟨xor_assoc⟩

def xorAll (count : Nat) (values : Fin count → Block) : Block :=
  Finset.univ.fold Bytes.xor zeroBlock values

def xorRest (count : Nat) (pivot : Fin count)
    (values : Fin count → Block) : Block :=
  (Finset.univ.erase pivot).fold Bytes.xor zeroBlock values

theorem xorAll_eq_pivot_xor_rest (values : Fin count → Block)
    (pivot : Fin count) :
    xorAll count values = Bytes.xor (values pivot) (xorRest count pivot values) := by
  unfold xorAll xorRest
  rw [show (Finset.univ : Finset (Fin count)) =
      insert pivot (Finset.univ.erase pivot) by simp]
  rw [Finset.fold_insert (by simp)]
  rw [Finset.erase_insert (by simp)]

theorem xorRest_congr {left right : Fin count → Block} (pivot : Fin count)
    (hequal : ∀ index, index ≠ pivot → left index = right index) :
    xorRest count pivot left = xorRest count pivot right := by
  unfold xorRest
  apply Finset.fold_congr
  intro index hmem
  exact hequal index (Finset.ne_of_mem_erase hmem)

theorem xor_cipher_eq_of_single_translation
    (sourcePayload targetPayload : Block) (source target : Fin count → Block)
    (pivot : Fin count)
    (hpivot : target pivot =
      IdealAffineTablePrivacy.translatePad sourcePayload targetPayload
        (source pivot))
    (hother : ∀ index, index ≠ pivot → target index = source index) :
    Bytes.xor targetPayload (xorAll count target) =
      Bytes.xor sourcePayload (xorAll count source) := by
  rw [xorAll_eq_pivot_xor_rest target pivot,
    xorAll_eq_pivot_xor_rest source pivot,
    xorRest_congr pivot hother]
  rw [hpivot]
  apply Vector.ext
  intro index hindex
  simp only [IdealAffineTablePrivacy.translatePad, Bytes.xor, Bytes.ofFn,
    Vector.getElem_ofFn, Vector.get_eq_getElem]
  generalize targetPayload[index] = a
  generalize sourcePayload[index] = b
  generalize (source pivot)[index] = c
  generalize (xorRest count pivot source)[index] = d
  rw [UInt8.xor_assoc a (b ^^^ c) d]
  rw [← UInt8.xor_assoc a a ((b ^^^ c) ^^^ d)]
  simp only [UInt8.xor_self, UInt8.zero_xor]
  exact UInt8.xor_assoc b c d

def aggregatePad (pairs : LabelPairs) (row : RowIndex)
    (chunk : Bool) : Block :=
  xorAll coordinateBitCount
    (fun index => pairs index (rowBits row index) (purpose row chunk))

def aggregateActivePad (labels : ActiveLabels) (row : RowIndex)
    (chunk : Bool) : Block :=
  xorAll coordinateBitCount (fun index => labels index (purpose row chunk))

theorem aggregateActivePad_selected (pairs : LabelPairs) (input : Input)
    (chunk : Bool) :
    aggregateActivePad (activeLabels pairs input) (rowIndex input) chunk =
      aggregatePad pairs (rowIndex input) chunk := by
  unfold aggregateActivePad aggregatePad activeLabels
  apply congrArg (xorAll coordinateBitCount)
  funext index
  rw [rowBits_rowIndex]

noncomputable def garbleRow (hidden : Hidden) (pairs : LabelPairs)
    (row : RowIndex) : Row :=
  let payload := encodeOutput (outputForRow hidden row)
  IdealAffineTable.row
    (firstBlock payload) (secondBlock payload)
    (aggregatePad pairs row false) (aggregatePad pairs row true)

def openRow (row : Row) (falsePad truePad : Block) : Row :=
  Bytes.append
    (Bytes.xor (firstBlock row) falsePad)
    (Bytes.xor (secondBlock row) truePad)

private theorem append_blocks_encodeOutput (output : Output) :
    Bytes.append (firstBlock (encodeOutput output))
        (secondBlock (encodeOutput output)) = encodeOutput output := by
  cases output <;> simp [encodeOutput]

@[simp] theorem openRow_garbleRow (hidden : Hidden) (pairs : LabelPairs)
    (row : RowIndex) :
    openRow (garbleRow hidden pairs row)
        (aggregatePad pairs row false) (aggregatePad pairs row true) =
      encodeOutput (outputForRow hidden row) := by
  unfold openRow garbleRow
  dsimp only
  unfold firstBlock secondBlock
  rw [IdealAffineTable.rowHalf_row_false,
    IdealAffineTable.rowHalf_row_true,
    Bytes.xor_cancel_right, Bytes.xor_cancel_right]
  exact append_blocks_encodeOutput _

@[ext] structure Artifact where
  rows : RowIndex → Row

noncomputable def garble (hidden : Hidden) (pairs : LabelPairs) : Artifact where
  rows := garbleRow hidden pairs

private def optionResult : Option Output → Except EvalError Output
  | some output => .ok output
  | none => .error .invalidLabels

def decodeEvaluated (plaintext : Row) : Except EvalError Output :=
  optionResult (decodeOutput plaintext)

private theorem decodeEvaluated_encodeOutput (output : Output) :
    decodeEvaluated (encodeOutput output) = .ok output :=
  congrArg optionResult (decodeOutput_encodeOutput output)

def evaluate (artifact : Artifact) (input : Input)
    (labels : ActiveLabels) : Except EvalError Output :=
  decodeEvaluated
    (openRow (artifact.rows (rowIndex input))
      (aggregateActivePad labels (rowIndex input) false)
      (aggregateActivePad labels (rowIndex input) true))

private theorem evaluate_eq (artifact : Artifact) (input : Input)
    (labels : ActiveLabels) :
    evaluate artifact input labels =
      decodeEvaluated
        (openRow (artifact.rows (rowIndex input))
          (aggregateActivePad labels (rowIndex input) false)
          (aggregateActivePad labels (rowIndex input) true)) := rfl

private theorem openSelected_garble (hidden : Hidden) (pairs : LabelPairs)
    (input : Input) :
    openRow ((garble hidden pairs).rows (rowIndex input))
        (aggregateActivePad (activeLabels pairs input) (rowIndex input) false)
        (aggregateActivePad (activeLabels pairs input) (rowIndex input) true) =
      encodeOutput (outputForRow hidden (rowIndex input)) := by
  rw [aggregateActivePad_selected, aggregateActivePad_selected]
  exact openRow_garbleRow hidden pairs (rowIndex input)

private theorem evaluate_garble_outputForRow (hidden : Hidden)
    (pairs : LabelPairs) (input : Input) :
    evaluate (garble hidden pairs) input (activeLabels pairs input) =
      .ok (outputForRow hidden (rowIndex input)) := by
  calc
    evaluate (garble hidden pairs) input (activeLabels pairs input) =
        decodeEvaluated
          (openRow ((garble hidden pairs).rows (rowIndex input))
            (aggregateActivePad (activeLabels pairs input) (rowIndex input) false)
            (aggregateActivePad (activeLabels pairs input) (rowIndex input) true)) :=
      evaluate_eq _ _ _
    _ = decodeEvaluated
          (encodeOutput (outputForRow hidden (rowIndex input))) :=
      congrArg decodeEvaluated (openSelected_garble hidden pairs input)
    _ = .ok (outputForRow hidden (rowIndex input)) :=
      decodeEvaluated_encodeOutput _

theorem evaluate_garble (hidden : Hidden) (pairs : LabelPairs) (input : Input) :
    evaluate (garble hidden pairs) input (activeLabels pairs input) =
      .ok (Profile.outputEquiv.symm (reference Profile hidden input)) := by
  rw [evaluate_garble_outputForRow, outputForRow_selected]

end

end GarblingPrize.Submission.TruthTable
