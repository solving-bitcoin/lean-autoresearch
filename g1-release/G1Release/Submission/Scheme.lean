import G1Release.Protected.Target
import G1Release.Submission.OffsetFamily
import G1Release.Submission.ProjectiveMap
import G1Release.Submission.RuntimeG1

namespace G1Release.Submission.Scheme

open GarblingPrize.Protected
open G1Release.Protected
open G1Release.Submission.BalancedTernary
open SecretRelease

local instance : AddCommGroup BN254.G1 := inferInstance

abbrev Hidden := Private
abbrev Word := BN254.Fq
abbrev Point := RuntimeG1.Point
abbrev Hash := SecretRelease.Hash
abbrev Label := SecretRelease.Label

def mapBytes : Nat := 178816
def claimedBytes : Nat := 161 * mapBytes

theorem claimedBytes_eq : claimedBytes = 28789376 := rfl

structure Artifact where
  bytes : ByteArray
  size_eq : bytes.size = claimedBytes

def runtimeOfGroup : BN254.G1 → Point
  | .zero => RuntimeG1.infinity
  | @WeierstrassCurve.Affine.Point.some _ _ _ x y h =>
      RuntimeG1.ofAffine ⟨x, y⟩ (by
        have hequation :=
          (BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
            BN254.discriminant_ne_zero).mpr h
        rw [WeierstrassCurve.Affine.equation_iff] at hequation
        simpa [HomogeneousRCBG1GroupLaw.AffineOnCurve, BN254.curve] using
          hequation.symm)

@[simp] theorem toPoint_runtimeOfGroup (point : BN254.G1) :
    RuntimeG1.toPoint (runtimeOfGroup point) = point := by
  cases point <;> rfl

def inputAffine (input : Input) : HomogeneousRCBG1GroupLaw.Affine :=
  ⟨(input.val.1.val : Word), (input.val.2.val : Word)⟩

theorem inputAffine_onCurve (input : Input) :
    HomogeneousRCBG1GroupLaw.AffineOnCurve (inputAffine input) := by
  change (input.val.1.val : Word) ^ 3 + 3 = (input.val.2.val : Word) ^ 2
  exact input.property.symm

def inputRuntime (input : Input) : Point :=
  RuntimeG1.ofAffine (inputAffine input) (inputAffine_onCurve input)

def inputG1 (input : Input) : BN254.G1 :=
  BN254.ofAffine input.val.1 input.val.2 input.property

@[simp] theorem toPoint_inputRuntime (input : Input) :
    RuntimeG1.toPoint (inputRuntime input) = inputG1 input := rfl

def digitSelector : Digit → Bool
  | .negative => true
  | .zero => false
  | .positive => true

def digitSign : Digit → HomogeneousRCB.Sign
  | .negative => .negative
  | .zero => .positive
  | .positive => .positive

def digitRuntime (digit : Digit) (input : Input) : Point :=
  match digit with
  | .negative =>
      RuntimeG1.ofAffine (HomogeneousRCBG1GroupLaw.negAffine (inputAffine input))
        (HomogeneousRCBG1GroupLaw.negAffine_onCurve (inputAffine input)
          (inputAffine_onCurve input))
  | .zero => RuntimeG1.infinity
  | .positive => inputRuntime input

theorem selectedInput_eq_digitRuntime (digit : Digit) (input : Input) :
    HomogeneousRCB.selectedInput (digitSelector digit) (digitSign digit)
        (RuntimeG1.encode (inputRuntime input)) =
      RuntimeG1.encode (digitRuntime digit input) := by
  cases digit with
  | negative =>
      simpa [digitSelector, digitSign, digitRuntime, inputRuntime,
        RuntimeG1.encode, RuntimeG1.ofAffine] using
        HomogeneousRCBG1GroupLaw.selectedInput_negative_eq_encode true
          (inputAffine input)
  | zero =>
      simpa [digitSelector, digitSign, digitRuntime, inputRuntime,
        RuntimeG1.encode, RuntimeG1.ofAffine, RuntimeG1.infinity] using
        HomogeneousRCBG1GroupLaw.selectedInput_positive_eq_encode false
          (inputAffine input)
  | positive =>
      simpa [digitSelector, digitSign, digitRuntime, inputRuntime,
        RuntimeG1.encode, RuntimeG1.ofAffine] using
        HomogeneousRCBG1GroupLaw.selectedInput_positive_eq_encode true
          (inputAffine input)

def curveC : Word := ProjectiveMap.curveC

def rawMap (offset : BN254.G1) (digit : Digit) (input : Input) :
    HomogeneousRCB.Point Word :=
  HomogeneousRCB.formula curveC
    (RuntimeG1.encode (runtimeOfGroup offset))
    (HomogeneousRCB.selectedInput (digitSelector digit) (digitSign digit)
      (RuntimeG1.encode (inputRuntime input)))

theorem rawMap_eq_addFormula (offset : BN254.G1) (digit : Digit)
    (input : Input) :
    rawMap offset digit input =
      HomogeneousRCBG1GroupLaw.addFormula
        (RuntimeG1.encode (runtimeOfGroup offset))
        (RuntimeG1.encode (digitRuntime digit input)) := by
  unfold rawMap HomogeneousRCBG1GroupLaw.addFormula curveC ProjectiveMap.curveC
  rw [selectedInput_eq_digitRuntime]

theorem rawMap_valid (offset : BN254.G1) (digit : Digit) (input : Input) :
    BN254.curve.toJacobian.Nonsingular
      (HomogeneousRCBG1GroupLaw.toJacobian (rawMap offset digit input)) := by
  rw [rawMap_eq_addFormula]
  exact HomogeneousRCBG1GroupLaw.toJacobian_formula_valid
    (runtimeOfGroup offset).1 (digitRuntime digit input).1
    (runtimeOfGroup offset).2 (digitRuntime digit input).2

theorem toPoint_digitRuntime (digit : Digit) (input : Input) :
    RuntimeG1.toPoint (digitRuntime digit input) =
      digit.value • inputG1 input := by
  cases digit with
  | negative =>
      calc
        RuntimeG1.toPoint (digitRuntime .negative input) =
            -RuntimeG1.toPoint (inputRuntime input) :=
          RuntimeG1.toPoint_negAffine (inputAffine input)
            (inputAffine_onCurve input)
        _ = -inputG1 input := congrArg Neg.neg (toPoint_inputRuntime input)
  | zero => rfl
  | positive =>
      simp [digitRuntime, Digit.value, toPoint_inputRuntime]

theorem decode_rawMap (offset : BN254.G1) (digit : Digit) (input : Input) :
    FormulaSemantics.Law.decode (rawMap offset digit input) =
      offset + digit.value • inputG1 input := by
  rw [rawMap_eq_addFormula]
  unfold RuntimeG1.encode
  rw [FormulaSemantics.Law.decode_formula
    (runtimeOfGroup offset).1 (digitRuntime digit input).1
    (runtimeOfGroup offset).2 (digitRuntime digit input).2]
  rw [← RuntimeG1.toPoint_eq_pointOfInput (runtimeOfGroup offset),
    ← RuntimeG1.toPoint_eq_pointOfInput (digitRuntime digit input),
    toPoint_runtimeOfGroup, toPoint_digitRuntime]

def zeroChainMasks : ProjectiveMap.ChainMasks Word where
  shared := 0
  xCross := 0
  xOuter := 0
  yCubic := 0
  yQuadratic := 0
  zSquare := 0
  zCross := 0
  zLinear := 0

def offsetAt {hidden : Hidden} (offsets : OffsetFamily.Fiber hidden)
    (index : Fin 161) : BN254.G1 :=
  offsets.values.get ⟨index.val, by rw [offsets.length_eq]; exact index.isLt⟩

def digitAt (hidden : Hidden) (index : Fin 161) : Digit :=
  (OffsetFamily.digits hidden).get index

def mapHidden (hidden : Hidden) (offsets : OffsetFamily.Fiber hidden)
    (index : Fin 161) : ProjectiveMap.Hidden where
  coefficients := ProjectiveMap.coefficients curveC
    (RuntimeG1.encode (runtimeOfGroup (offsetAt offsets index)))
    (digitSelector (digitAt hidden index)) (digitSign (digitAt hidden index))
  chainMasks := zeroChainMasks

def mapMasks (hidden : Hidden) (offsets : OffsetFamily.Fiber hidden)
    (index : Fin 161) (kind : ProjectiveMap.TableKind) :
    AffineTable.MaskFiber ((mapHidden hidden offsets index).params kind).constant :=
  AffineTable.canonicalMasks _

def xPairs (keys : Fin 512 → Pair) : Fin 254 → Bool → Label :=
  fun i b => (keys ⟨i.val, by omega⟩).get b

def yPairs (keys : Fin 512 → Pair) : Fin 254 → Bool → Label :=
  fun i b => (keys ⟨256 + i.val, by omega⟩).get b

def xBits (input : Input) : Fin 254 → Bool :=
  fun i => input.val.1.val.testBit i.val

def yBits (input : Input) : Fin 254 → Bool :=
  fun i => input.val.2.val.testBit i.val

def xLabels (keys : Fin 512 → Pair) (input : Input) : Fin 254 → Label :=
  fun i => xPairs keys i (xBits input i)

def yLabels (keys : Fin 512 → Pair) (input : Input) : Fin 254 → Label :=
  fun i => yPairs keys i (yBits input i)

def garbleMaps (hash : Hash) (hidden : Hidden) (keys : Fin 512 → Pair) :
    Fin 161 → ProjectiveMap.Artifact :=
  fun index =>
    ProjectiveMap.garble hash index.val (xPairs keys) (yPairs keys)
      (mapHidden hidden (OffsetFamily.canonical hidden) index)
      (mapMasks hidden (OffsetFamily.canonical hidden) index)

def encodeFrom (maps : Fin 161 → ProjectiveMap.Artifact) :
    (n : Nat) → n ≤ 161 → ByteArray
  | 0, _ => ByteArray.empty
  | n + 1, h =>
      encodeFrom maps n (Nat.le_of_succ_le h) ++
        ProjectiveMap.encode (maps ⟨n, h⟩)

theorem encodeFrom_size (maps : Fin 161 → ProjectiveMap.Artifact)
    (n : Nat) (hn : n ≤ 161) :
    (encodeFrom maps n hn).size = n * mapBytes := by
  induction n with
  | zero => simp [encodeFrom]
  | succ n ih =>
      simp [encodeFrom, ByteArray.size_append, ProjectiveMap.encode_size,
        mapBytes, ih, ProjectiveMap.mapByteCount, ProjectiveMap.tableByteCount,
        AffineTable.tableByteCount]
      ring

def garble (hash : Hash) (hidden : Hidden) (keys : Fin 512 → Pair) : Artifact :=
  ⟨encodeFrom (garbleMaps hash hidden keys) 161 (Nat.le_refl 161), by
    have := encodeFrom_size (garbleMaps hash hidden keys) 161 (Nat.le_refl 161)
    simpa [claimedBytes] using this⟩

def encode (artifact : Artifact) : ByteArray := artifact.bytes

theorem encode_size (artifact : Artifact) :
    (encode artifact).size = claimedBytes := artifact.size_eq

theorem mapBytes_eq_mapByteCount : mapBytes = ProjectiveMap.mapByteCount := by
  simp [mapBytes, ProjectiveMap.mapByteCount, ProjectiveMap.tableByteCount,
    AffineTable.tableByteCount]

theorem encodeFrom_extract (maps : Fin 161 → ProjectiveMap.Artifact)
    (n : Nat) (hn : n ≤ 161) (i : Fin n) :
    (encodeFrom maps n hn).extract (i.val * mapBytes) ((i.val + 1) * mapBytes) =
      ProjectiveMap.encode (maps ⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
      have hn' : n ≤ 161 := Nat.le_of_succ_le hn
      have hsz : (encodeFrom maps n hn').size = n * mapBytes :=
        encodeFrom_size maps n hn'
      unfold encodeFrom
      have hmap : (ProjectiveMap.encode (maps ⟨n, hn⟩)).size = mapBytes := by
        simpa [mapBytes_eq_mapByteCount] using ProjectiveMap.encode_size _
      rcases (Nat.lt_succ_iff_lt_or_eq).mp i.isLt with hlt | heq
      · have hj : (i.val + 1) * mapBytes ≤ n * mapBytes := by
          have : i.val + 1 ≤ n := Nat.succ_le_of_lt hlt
          exact Nat.mul_le_mul_right mapBytes this
        have hi : i.val * mapBytes ≤ n * mapBytes :=
          Nat.mul_le_mul_right mapBytes (Nat.le_of_lt hlt)
        have : (encodeFrom maps n hn' ++ ProjectiveMap.encode (maps ⟨n, hn⟩)).extract
            (i.val * mapBytes) ((i.val + 1) * mapBytes) =
            (encodeFrom maps n hn').extract (i.val * mapBytes) ((i.val + 1) * mapBytes) := by
          have hbound : (i.val + 1) * mapBytes ≤ (encodeFrom maps n hn').size := by
            rw [hsz]; exact hj
          rw [ByteArray.extract_append]
          have hempty : (ProjectiveMap.encode (maps ⟨n, hn⟩)).extract
              (i.val * mapBytes - (encodeFrom maps n hn').size)
              ((i.val + 1) * mapBytes - (encodeFrom maps n hn').size) =
              ByteArray.empty := by
            rw [ByteArray.extract_eq_empty_iff, hsz]
            have : (i.val + 1) * mapBytes - n * mapBytes = 0 := Nat.sub_eq_zero_of_le hj
            omega
          rw [hempty, ByteArray.append_empty]
        rw [this, ih hn' ⟨i.val, hlt⟩]
      · have hi : i.val = n := heq
        have hchunk :
            (encodeFrom maps n hn' ++ ProjectiveMap.encode (maps ⟨n, hn⟩)).extract
              (n * mapBytes) ((n + 1) * mapBytes) =
              ProjectiveMap.encode (maps ⟨n, hn⟩) := by
          refine ByteArray.extract_append_eq_right hsz.symm ?_
          rw [hsz, hmap]
          ring
        have hidx : (⟨i.val, Nat.lt_of_lt_of_le i.isLt hn⟩ : Fin 161) = ⟨n, hn⟩ :=
          Fin.ext hi
        simpa [hi, hidx] using hchunk

def decode (bytes : ByteArray) : Option Artifact :=
  if h : bytes.size = claimedBytes then some ⟨bytes, h⟩ else none

theorem decode_encode (artifact : Artifact) :
    decode (encode artifact) = some artifact := by
  unfold decode encode
  rw [dif_pos artifact.size_eq]

theorem encode_decode {bytes : ByteArray} {artifact : Artifact}
    (h : decode bytes = some artifact) : encode artifact = bytes := by
  unfold decode at h
  split at h
  · cases h; rfl
  · contradiction

def mapAt (artifact : Artifact) (i : Fin 161) : Option ProjectiveMap.Artifact :=
  ProjectiveMap.decode (artifact.bytes.extract (i.val * mapBytes) ((i.val + 1) * mapBytes))

def readLabel (active : ByteArray) (i : Fin 512) : Label :=
  let chunk := active.extract (32 * i.val) (32 * i.val + 32)
  if h : chunk.size = 32 then ⟨chunk.data, h⟩
  else Vector.replicate 32 0

def evalXLabels (active : ByteArray) : Fin 254 → Label :=
  fun i => readLabel active ⟨i.val, by omega⟩

def evalYLabels (active : ByteArray) : Fin 254 → Label :=
  fun i => readLabel active ⟨256 + i.val, by omega⟩

def finish : Option (ProjectiveMap.Coordinates Word) → Option Point
  | none => none
  | some coords =>
      match RuntimeG1.normalize { x := coords.x, y := coords.y, z := coords.z } with
      | .ok p => some p
      | .error _ => none

@[simp] theorem finish_some (coords : ProjectiveMap.Coordinates Word) :
    finish (some coords) =
      match RuntimeG1.normalize { x := coords.x, y := coords.y, z := coords.z } with
      | .ok p => some p
      | .error _ => none := rfl

theorem finish_ofHomogeneous (point : HomogeneousRCB.Point Word) :
    finish (some (ProjectiveMap.Coordinates.ofHomogeneous point)) =
      match RuntimeG1.normalize point with
      | .ok p => some p
      | .error _ => none := rfl

def evaluateMap (hash : Hash) (index : Fin 161) (map : ProjectiveMap.Artifact)
    (input : Input) (active : ByteArray) : Option Point :=
  finish (ProjectiveMap.evaluate hash index.val map
      (input.val.1.val : Word) (input.val.2.val : Word)
      (xBits input) (yBits input)
      (evalXLabels active) (evalYLabels active))

def evaluateOne (hash : Hash) (artifact : Artifact) (input : Input)
    (active : ByteArray) (index : Fin 161) : Option Point := do
  let m ← mapAt artifact index
  evaluateMap hash index m input active

def evaluateMaps (hash : Hash) (artifact : Artifact) (input : Input)
    (active : ByteArray) (indices : List (Fin 161)) : Option (List Point) :=
  indices.mapM (evaluateOne hash artifact input active)

def evaluate (hash : Hash) (artifact : Artifact) (input : Input)
    (active : ByteArray) : Option ByteArray :=
  if active.size != 16384 then none
  else do
    let points ← evaluateMaps hash artifact input active (List.finRange 161)
    match RuntimeG1.recompose points with
    | .error _ => none
    | .ok result => some (encodeOutput (RuntimeG1.toOutput result))

def scheme : SecretRelease.Scheme challenge where
  Artifact := Artifact
  randomnessBytes := 32
  garble := fun h _ p ik _ => garble h p ik
  encode := encode
  decode := decode
  evaluate := fun h art x active => evaluate h art x active

@[simp] theorem scheme_encode : scheme.encode = encode := rfl
@[simp] theorem scheme_decode : scheme.decode = decode := rfl
@[simp] theorem scheme_evaluate (hash : Hash) (artifact : scheme.Artifact)
    (input : challenge.Input) (active : ByteArray) :
    scheme.evaluate hash artifact input active =
      evaluate hash artifact input active := rfl
@[simp] theorem scheme_garble (hash : Hash)
    (coins : SecretRelease.Bytes scheme.randomnessBytes)
    (hidden : challenge.Private) (keys : challenge.inputs.Keys)
    (ok : challenge.outputs.Keys) :
    scheme.garble hash coins hidden keys ok = garble hash hidden keys := rfl

theorem fq_lt_two_pow_254 (x : CanonicalFq) : x.val < 2 ^ 254 :=
  lt_trans x.isLt (by norm_num [baseFieldModulus])

theorem decodeBits_xBits (input : Input) :
    AffineTable.decodeBits (xBits input) = (input.val.1.val : Word) :=
  AffineTable.decodeBits_testBit _ (fq_lt_two_pow_254 input.val.1)

theorem decodeBits_yBits (input : Input) :
    AffineTable.decodeBits (yBits input) = (input.val.2.val : Word) :=
  AffineTable.decodeBits_testBit _ (fq_lt_two_pow_254 input.val.2)

theorem onCurve_decodeBits (input : Input) :
    AffineTable.decodeBits (yBits input) ^ 2 =
      AffineTable.decodeBits (xBits input) ^ 3 + 3 := by
  rw [decodeBits_xBits, decodeBits_yBits]
  exact input.property

theorem artifactBound (hash : Hash) (coins : SecretRelease.Bytes 32) (p : Hidden)
    (ik : Fin 512 → Pair) (ok : Unit) :
    (scheme.garbleBytes hash coins p ik ok).size ≤ claimedBytes := by
  change (encode (garble hash p ik)).size ≤ claimedBytes
  rw [encode_size]

theorem coefficients_xX (hidden : Hidden) (offsets : OffsetFamily.Fiber hidden)
    (index : Fin 161) :
    (mapHidden hidden offsets index).coefficients.xX =
      -(2 * curveC * (mapHidden hidden offsets index).coefficients.zYY) :=
  ProjectiveMap.coefficients_xX curveC _ _ _

theorem coefficients_zXX (hidden : Hidden) (offsets : OffsetFamily.Fiber hidden)
    (index : Fin 161) :
    (mapHidden hidden offsets index).coefficients.zXX =
      3 * (mapHidden hidden offsets index).coefficients.xYY :=
  ProjectiveMap.coefficients_zXX curveC _ _ _

theorem polynomial_mapHidden (hidden : Hidden) (offsets : OffsetFamily.Fiber hidden)
    (index : Fin 161) (input : Input) :
    ProjectiveMap.polynomial (mapHidden hidden offsets index).coefficients
        (input.val.1.val : Word) (input.val.2.val : Word) =
      ProjectiveMap.Coordinates.ofHomogeneous
        (rawMap (offsetAt offsets index) (digitAt hidden index) input) :=
  ProjectiveMap.polynomial_coefficients curveC _ _ _ _ _

theorem evaluate_garble_mapHidden (hash : Hash) (hidden : Hidden)
    (offsets : OffsetFamily.Fiber hidden) (keys : Fin 512 → Pair)
    (input : Input) (index : Fin 161) :
    ProjectiveMap.evaluate hash index.val
        (ProjectiveMap.garble hash index.val (xPairs keys) (yPairs keys)
          (mapHidden hidden offsets index) (mapMasks hidden offsets index))
        (AffineTable.decodeBits (xBits input))
        (AffineTable.decodeBits (yBits input))
        (xBits input) (yBits input)
        (fun i => xPairs keys i (xBits input i))
        (fun i => yPairs keys i (yBits input i)) =
      some (ProjectiveMap.polynomial (mapHidden hidden offsets index).coefficients
        (AffineTable.decodeBits (xBits input))
        (AffineTable.decodeBits (yBits input))) :=
  ProjectiveMap.evaluate_garble hash index.val (xPairs keys) (yPairs keys)
    (mapHidden hidden offsets index) (mapMasks hidden offsets index)
    (xBits input) (yBits input) (onCurve_decodeBits input)
    (coefficients_xX hidden offsets index)
    (coefficients_zXX hidden offsets index)

theorem mapAt_garble (hash : Hash) (hidden : Hidden) (keys : Fin 512 → Pair)
    (i : Fin 161) :
    mapAt (garble hash hidden keys) i = some (garbleMaps hash hidden keys i) := by
  unfold mapAt garble encodeFrom
  -- use extract lemma on the packed maps
  change ProjectiveMap.decode
      ((encodeFrom (garbleMaps hash hidden keys) 161 (Nat.le_refl 161)).extract
        (i.val * mapBytes) ((i.val + 1) * mapBytes)) =
    some (garbleMaps hash hidden keys i)
  rw [encodeFrom_extract (garbleMaps hash hidden keys) 161 (Nat.le_refl 161) i]
  exact ProjectiveMap.decode_encode _

end G1Release.Submission.Scheme
