import GarblingPrize.Submission.TruthTablePrivacy

namespace GarblingPrize.Submission.TruthTableCodec

open GarblingPrize.Protected
open GarblingPrize.Submission.TruthTable

def flatRowNat (index : Fin artifactByteCount) : Nat :=
  index.val / rowByteCount

def flatByte (index : Fin artifactByteCount) : Fin rowByteCount :=
  ⟨index.val % rowByteCount, by
    apply Nat.mod_lt
    norm_num [rowByteCount]⟩

def flatRowBits (index : Fin artifactByteCount) : RowIndex :=
  fun bit => (flatRowNat index).testBit bit.val

private theorem flatRowNat_lt (index : Fin artifactByteCount) :
    flatRowNat index < tableCount := by
  unfold flatRowNat
  apply (Nat.div_lt_iff_lt_mul (by norm_num [rowByteCount])).2
  exact index.isLt

set_option maxRecDepth 2048 in
@[simp] theorem ofBits_flatRowBits (index : Fin artifactByteCount) :
    Nat.ofBits (flatRowBits index) = flatRowNat index := by
  unfold flatRowBits
  rw [Nat.ofBits_testBit, Nat.mod_eq_of_lt]
  have hbound := flatRowNat_lt index
  change flatRowNat index < 2 ^ coordinateBitCount at hbound
  exact hbound

def flatIndex (row : RowIndex) (byte : Fin rowByteCount) :
    Fin artifactByteCount :=
  ⟨Nat.ofBits row * rowByteCount + byte.val, by
    have hrow : Nat.ofBits row < tableCount := by
      simpa [tableCount] using Nat.ofBits_lt_two_pow row
    change Nat.ofBits row * rowByteCount + byte.val <
      tableCount * rowByteCount
    calc
      Nat.ofBits row * rowByteCount + byte.val <
          Nat.ofBits row * rowByteCount + rowByteCount :=
        Nat.add_lt_add_left byte.isLt _
      _ = (Nat.ofBits row + 1) * rowByteCount := by ring
      _ ≤ tableCount * rowByteCount :=
        Nat.mul_le_mul_right rowByteCount (Nat.succ_le_iff.mpr hrow)⟩

@[simp] theorem flatRowBits_flatIndex (row : RowIndex)
    (byte : Fin rowByteCount) : flatRowBits (flatIndex row byte) = row := by
  funext bit
  change ((Nat.ofBits row * rowByteCount + byte.val) / rowByteCount).testBit
      bit.val = row bit
  have hdiv :
      (Nat.ofBits row * rowByteCount + byte.val) / rowByteCount =
        Nat.ofBits row := by
    rw [Nat.mul_comm (Nat.ofBits row) rowByteCount,
      Nat.mul_add_div (by norm_num [rowByteCount]),
      Nat.div_eq_of_lt byte.isLt, Nat.add_zero]
  rw [hdiv]
  exact Nat.testBit_ofBits_lt row bit.val bit.isLt

@[simp] theorem flatByte_flatIndex (row : RowIndex)
    (byte : Fin rowByteCount) : flatByte (flatIndex row byte) = byte := by
  apply Fin.ext
  change (Nat.ofBits row * rowByteCount + byte.val) % rowByteCount = byte.val
  rw [Nat.mul_add_mod_of_lt byte.isLt]

@[simp] theorem flatIndex_flatParts (index : Fin artifactByteCount) :
    flatIndex (flatRowBits index) (flatByte index) = index := by
  apply Fin.ext
  change Nat.ofBits (flatRowBits index) * rowByteCount +
      index.val % rowByteCount = index.val
  rw [ofBits_flatRowBits]
  unfold flatRowNat
  rw [Nat.mul_comm]
  exact Nat.div_add_mod index.val rowByteCount

def encodeFixed (artifact : Artifact) : Bytes artifactByteCount :=
  Bytes.ofFn fun index =>
    (artifact.rows (flatRowBits index)).get (flatByte index)

def decodeFixed (bytes : Bytes artifactByteCount) : Artifact where
  rows := fun row => Bytes.ofFn fun byte => bytes.get (flatIndex row byte)

/-- Read exactly one truth-table row from the packed artifact.  The ranked
evaluator uses this projection directly, so Lean never needs to materialize
or compare the full `2^512`-row decoded function. -/
def selectedRow (bytes : Bytes artifactByteCount) (row : RowIndex) : Row :=
  Bytes.ofFn fun byte => bytes.get (flatIndex row byte)

private theorem bytes_ofFn_get (value : Bytes count) :
    Bytes.ofFn (fun index => value.get index) = value := by
  apply Vector.ext
  intro index hindex
  simp [Bytes.ofFn, Vector.get_eq_getElem]

@[simp] theorem decodeFixed_encodeFixed (artifact : Artifact) :
    decodeFixed (encodeFixed artifact) = artifact := by
  apply Artifact.ext
  funext row
  rw [← bytes_ofFn_get (artifact.rows row)]
  apply congrArg Bytes.ofFn
  funext byte
  simp only [encodeFixed, Bytes.ofFn, Vector.get_ofFn]
  rw [flatRowBits_flatIndex, flatByte_flatIndex]

@[simp] theorem encodeFixed_decodeFixed (bytes : Bytes artifactByteCount) :
    encodeFixed (decodeFixed bytes) = bytes := by
  rw [← bytes_ofFn_get bytes]
  apply congrArg Bytes.ofFn
  funext index
  simp only [decodeFixed, Bytes.ofFn, Vector.get_ofFn]
  rw [flatIndex_flatParts]

@[simp] theorem selectedRow_encodeFixed (artifact : Artifact)
    (row : RowIndex) :
    selectedRow (encodeFixed artifact) row = artifact.rows row := by
  change (decodeFixed (encodeFixed artifact)).rows row = artifact.rows row
  rw [decodeFixed_encodeFixed]

/-- Evaluate only the selected packed row. -/
noncomputable def evaluateFixed (bytes : Bytes artifactByteCount)
    (input : Input) (labels : ActiveLabels) : Except EvalError Output :=
  TruthTable.decodeEvaluated
    (TruthTable.openRow (selectedRow bytes (TruthTable.rowIndex input))
      (TruthTable.aggregateActivePad labels (TruthTable.rowIndex input) false)
      (TruthTable.aggregateActivePad labels (TruthTable.rowIndex input) true))

@[simp] theorem evaluateFixed_encodeFixed (artifact : Artifact)
    (input : Input) (labels : ActiveLabels) :
    evaluateFixed (encodeFixed artifact) input labels =
      evaluate artifact input labels := by
  unfold evaluateFixed evaluate
  rw [selectedRow_encodeFixed]

def encode (artifact : Artifact) : ByteArray :=
  (encodeFixed artifact).toByteArray

private def decodeParsed : Option (Bytes artifactByteCount) →
    Except DecodeError Artifact
  | none => .error .malformedArtifact
  | some bytes => .ok (decodeFixed bytes)

def decode (input : ByteArray) : Except DecodeError Artifact :=
  decodeParsed (Bytes.ofByteArray? artifactByteCount input)

@[simp] theorem encode_size (artifact : Artifact) :
    (encode artifact).size = artifactByteCount := by
  simp [encode]

@[simp] theorem decode_encode (artifact : Artifact) :
    decode (encode artifact) = .ok artifact := by
  calc
    decode (encode artifact) =
        decodeParsed (some (encodeFixed artifact)) :=
      congrArg decodeParsed (Bytes.ofByteArray?_toByteArray (encodeFixed artifact))
    _ = .ok (decodeFixed (encodeFixed artifact)) := rfl
    _ = .ok artifact := congrArg Except.ok (decodeFixed_encodeFixed artifact)

theorem encode_decode {input : ByteArray} {artifact : Artifact}
    (hdecode : decode input = .ok artifact) : encode artifact = input := by
  cases hparse : Bytes.ofByteArray? artifactByteCount input with
  | none =>
      have hparsed := congrArg decodeParsed hparse
      have himpossible :
          decodeParsed none = .ok artifact := hparsed.symm.trans hdecode
      cases himpossible
  | some bytes =>
      have hparsed := congrArg decodeParsed hparse
      have hdecoded : decodeParsed (some bytes) = .ok artifact :=
        hparsed.symm.trans hdecode
      have hartifact : decodeFixed bytes = artifact :=
        Except.ok.inj hdecoded
      subst artifact
      calc
        encode (decodeFixed bytes) =
            (encodeFixed (decodeFixed bytes)).toByteArray := rfl
        _ = bytes.toByteArray :=
          congrArg Bytes.toByteArray (encodeFixed_decodeFixed bytes)
        _ = input := (Bytes.ofByteArray?_eq_some_iff.mp hparse).symm

end GarblingPrize.Submission.TruthTableCodec
