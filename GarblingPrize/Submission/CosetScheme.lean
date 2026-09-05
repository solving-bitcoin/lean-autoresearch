import GarblingPrize.Submission.CosetFamilyArtifact
import GarblingPrize.Submission.CosetRandomness
import GarblingPrize.Submission.GLVHintScheme

namespace GarblingPrize.Submission.CosetScheme

/-! The complete norm-seven scheme with eight base-field tables per map.
The translated x coordinate rationally recovers the original group point;
91 independent coset maps are recomposed by the established GLV radix law. -/

open GarblingPrize.Protected
open EisensteinRadix GLVCompactScheme
open CosetCoordinates FourAffineQuotient

abbrev Word := BN254.Fq
abbrev Point := RuntimeG1.Point
abbrev Randomness := CosetRandomness.Randomness
abbrev randomnessFromOracle := CosetRandomness.randomnessFromOracle
abbrev Artifact := CosetFamilyArtifact.Artifact 91
abbrev Coin := HintAffineTable.Coin
abbrev Coins := BitIndex → Purpose → Coin
abbrev coinModulus := GLVHintScheme.coinModulus
abbrev coinPurpose := GLVHintScheme.coinPurpose
abbrev coinsFromOracle := GLVHintScheme.coinsFromOracle

local instance concreteGroup : AddCommGroup BN254.G1 := BN254.bn254.addCommGroup
local instance profileGroup : AddCommGroup Profile.G1 := concreteGroup

def wireKind (kind : CosetHintMap.TableKind) : GLVProjectiveMap.TableKind :=
  CosetHintMap.inputFor kind .xLinear .xOuter

def tableWire (kind : CosetHintMap.TableKind) (row : HintAffineTable.RowIndex) : BitIndex :=
  GLVCompactPrivacy.tableWire (wireKind kind) row

def tableIndex (kind : CosetHintMap.TableKind) (wire : BitIndex) : Option HintAffineTable.RowIndex :=
  GLVCompactPrivacy.tableIndex (wireKind kind) wire

def bitsFor (kind : CosetHintMap.TableKind) (input : Input) : HintAffineTable.RowIndex → Bool :=
  CosetHintMap.inputFor kind (xBits input) (yBits input)

@[simp] theorem tableIndex_tableWire (kind : CosetHintMap.TableKind) (row : HintAffineTable.RowIndex) :
    tableIndex kind (tableWire kind row) = some row := GLVCompactPrivacy.tableIndex_tableWire _ _

theorem inputBit_tableWire (kind : CosetHintMap.TableKind) (input : Input) (row : HintAffineTable.RowIndex) :
    inputBit input (tableWire kind row) = bitsFor kind input row := by
  rw [tableWire, GLVCompactPrivacy.inputBit_tableWire]
  fin_cases kind <;> rfl

def tableCoins (coins : Coins) (index : Fin 91) (kind : CosetHintMap.TableKind) :
    HintAffineTable.RowIndex → Coin :=
  fun row => coins (tableWire kind row) (CosetHintMap.purpose index.val kind)

def mapBase (hidden : Hidden) (randomness : Randomness hidden) (index : Fin 91) : Base K :=
  CosetGLV.mapBase (offsetAt randomness.offsets index) (digitAt hidden index)

def mapParams (hidden : Hidden) (randomness : Randomness hidden) (index : Fin 91)
    (kind : CosetHintMap.TableKind) : IdealAffineTable.Params :=
  CosetHintMap.params (mapBase hidden randomness index) (randomness.states index) kind

def garble (hidden : Hidden) (randomness : Randomness hidden) (coins : Coins) (pairs : LabelPairs) :
    Artifact where
  maps := fun index => CosetHintMap.garble index.val (xPairs pairs) (yPairs pairs)
    (mapBase hidden randomness index) (randomness.states index) (tableCoins coins index)

def garbleWithOracle (hidden : Hidden) (oracle : InternalOracle) (pairs : LabelPairs) : Artifact :=
  garble hidden (randomnessFromOracle hidden oracle) (coinsFromOracle oracle) pairs

theorem garbleWithOracle_eq (hidden : Hidden) (oracle : InternalOracle) (pairs : LabelPairs) :
    garbleWithOracle hidden oracle pairs =
      garble hidden (randomnessFromOracle hidden oracle) (coinsFromOracle oracle) pairs := rfl

def finish (x : Word) (values : Option (Opened K)) : Except EvalError Point :=
  match values with
  | none => .error .internalFailure
  | some values => match CosetCoordinates.decode (reconstruct values (C x)) with
    | none => .error .internalFailure
    | some point => .ok point

theorem finish_correct (x : Word) (values : Opened K) (point : Point)
    (h : CosetCoordinates.decode (reconstruct values (C x)) = some point) :
    finish x (some values) = .ok point := by
  dsimp only [finish]
  rw [h]

def evaluateMap (index : Fin 91) (artifact : CosetHintMap.Artifact)
    (input : Input) (labels : ActiveLabels) : Except EvalError Point :=
  finish (input.x.val : Word) (CosetHintMap.evaluate index.val artifact (xBits input) (yBits input)
    (xLabels labels) (yLabels labels))

theorem evaluate_openings (index : Fin 91) (base : Base K) (state : State K)
    (coins : CosetHintMap.Coins) (pairs : LabelPairs) (input : Input) :
    CosetHintMap.evaluate index.val
      (CosetHintMap.garble index.val (xPairs pairs) (yPairs pairs) base state coins)
      (xBits input) (yBits input) (xLabels (activeLabels pairs input))
      (yLabels (activeLabels pairs input)) =
      some (opened base state (C (input.x.val : Word)) (C (input.y.val : Word))) := by
  rw [active_xLabels, active_yLabels, CosetHintMap.evaluate_garble,
    decodeBits_xBits, decodeBits_yBits]

def evaluateMaps (artifact : Artifact) (input : Input) (labels : ActiveLabels) :
    List (Fin 91) → Except EvalError (List Point)
  | [] => .ok []
  | index :: tail => do
      let point ← evaluateMap index (artifact.maps index) input labels
      let points ← evaluateMaps artifact input labels tail
      pure (point :: points)

def evaluate (artifact : Artifact) (input : Input) (labels : ActiveLabels) : Except EvalError Profile.Output := do
  let points ← evaluateMaps artifact input labels (List.finRange 91)
  let result ← RuntimeG1.recomposeAlpha points
  pure (show Profile.Output from RuntimeG1.toOutput result)

set_option maxRecDepth 4096 in
theorem evaluateMap_garble (hidden : Hidden) (randomness : Randomness hidden)
    (coins : Coins) (pairs : LabelPairs) (input : Input) (index : Fin 91) :
    ∃ result : Point,
      evaluateMap index ((garble hidden randomness coins pairs).maps index) input
          (activeLabels pairs input) = Except.ok result ∧
        RuntimeG1.toPoint result =
          EisensteinFullWidth.mapOutput (offsetAt randomness.offsets index)
            (digitAt hidden index) (-inputG1 input) := by
  refine ⟨runtimeOfGroup (EisensteinFullWidth.mapOutput (offsetAt randomness.offsets index)
    (digitAt hidden index) (-inputG1 input)), ?_, toPoint_runtimeOfGroup _⟩
  change finish (input.x.val : Word) (CosetHintMap.evaluate index.val
    (CosetHintMap.garble index.val (xPairs pairs) (yPairs pairs)
      (mapBase hidden randomness index) (randomness.states index) (tableCoins coins index))
    (xBits input) (yBits input) (xLabels (activeLabels pairs input))
    (yLabels (activeLabels pairs input))) = _
  rw [evaluate_openings]
  exact finish_correct _ _ _ (CosetGLV.decode_openings _ _ input (randomness.states index))

theorem evaluateMaps_garble (hidden : Hidden) (randomness : Randomness hidden)
    (coins : Coins) (pairs : LabelPairs) (input : Input) (indices : List (Fin 91)) :
    ∃ results : List Point,
      evaluateMaps (garble hidden randomness coins pairs) input
          (activeLabels pairs input) indices = .ok results ∧
        results.map RuntimeG1.toPoint =
          indices.map fun index =>
            EisensteinFullWidth.mapOutput (offsetAt randomness.offsets index)
              (digitAt hidden index) (-inputG1 input) := by
  induction indices with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons index indices ih =>
      obtain ⟨point, hpoint, hpointValue⟩ :=
        evaluateMap_garble hidden randomness coins pairs input index
      obtain ⟨points, hpoints, hpointsValue⟩ := ih
      refine ⟨point :: points, ?_, ?_⟩
      · unfold evaluateMaps
        rw [hpoint, hpoints]
        rfl
      · simp only [List.map_cons]
        rw [hpointValue, hpointsValue]

theorem artifactCorrect (hidden : Hidden) (randomness : Randomness hidden)
    (coins : Coins) (pairs : LabelPairs) (input : Input) :
    ∃ output : Profile.Output,
      evaluate (garble hidden randomness coins pairs) input
          (activeLabels pairs input) = .ok output ∧
        Profile.outputEquiv output = reference Profile hidden input := by
  obtain ⟨points, hpoints, hpointsValue⟩ :=
    evaluateMaps_garble hidden randomness coins pairs input (List.finRange 91)
  obtain ⟨result, hresult, hresultValue⟩ :=
    RuntimeG1.recomposeAlpha_correct points
  refine ⟨show Profile.Output from RuntimeG1.toOutput result, ?_, ?_⟩
  · unfold evaluate
    rw [hpoints]
    change (do
      let result ← RuntimeG1.recomposeAlpha points
      pure (RuntimeG1.toOutput result)) = _
    rw [hresult]
    rfl
  · change BN254.CanonicalOutput.toPoint (RuntimeG1.toOutput result) = _
    rw [RuntimeG1.output_toPoint, hresultValue, hpointsValue,
      fullMapOutputs]
    change EisensteinFullWidth.outputList randomness.offsets.values
      (GLVOffsetFamily.digits hidden) (-inputG1 input) =
        GLVOffsetFamily.qPoint hidden + hidden.r.val • inputG1 input
    have hsemantic := EisensteinFullWidth.output_scalar
      randomness.offsets.values hidden.r (-inputG1 input)
      randomness.offsets.length_eq
    unfold GLVOffsetFamily.digits
    rw [hsemantic, randomness.offsets.total_eq]
    rw [EisensteinFullWidth.point_nsmul_neg]
    abel

def encodeArtifact : Artifact → ByteArray := CosetFamilyArtifact.encode

/-- Native execution may build the independent map encodings concurrently.
The logical scheme and all privacy proofs continue to see the canonical
sequential encoder. -/
def encodeArtifactParallel : Artifact → ByteArray :=
  CosetFamilyArtifact.encodeParallel

@[csimp] theorem encodeArtifact_eq_parallel :
    encodeArtifact = encodeArtifactParallel := by
  funext artifact
  simp [encodeArtifact, encodeArtifactParallel]

def decodeArtifact (bytes : ByteArray) : Except DecodeError Artifact :=
  match CosetFamilyArtifact.decode 91 bytes with
  | .ok artifact => .ok artifact
  | .error .trailingBytes => .error .trailingBytes
  | .error _ => .error .malformedArtifact

def scheme : Scheme Profile :=
  Scheme.ofFunctions Artifact garbleWithOracle evaluate encodeArtifact
    decodeArtifact

theorem codec : CodecLaws scheme := by
  apply Scheme.codecLaws_ofFunctions
  · intro artifact
    unfold decodeArtifact encodeArtifact
    rw [CosetFamilyArtifact.decode_encode]
  · intro bytes artifact hdecode
    unfold decodeArtifact at hdecode
    cases hfamily : CosetFamilyArtifact.decode 91 bytes with
    | error error =>
        cases error <;> simp [hfamily] at hdecode
    | ok decoded =>
        have hdecoded : decoded = artifact := by simpa [hfamily] using hdecode
        subst decoded
        exact CosetFamilyArtifact.encode_decode hfamily

theorem correct : Correct scheme := by
  apply Scheme.correct_ofFunctions Artifact garbleWithOracle evaluate
    encodeArtifact decodeArtifact codec
  intro hidden oracle pairs input
  rw [garbleWithOracle_eq]
  exact artifactCorrect hidden (randomnessFromOracle hidden oracle) (coinsFromOracle oracle) pairs input

def claimedBytes : Nat := 5940480

set_option maxRecDepth 4096 in
theorem artifactBound (hidden : Hidden) (randomness : Randomness hidden)
    (coins : Coins) (pairs : LabelPairs) :
    (CosetFamilyArtifact.encode (garble hidden randomness coins pairs)).size ≤
      claimedBytes := by
  rw [CosetFamilyArtifact.encode_size, CosetFamilyArtifact.ninetyOne_byteCount]
  rfl

set_option maxRecDepth 4096 in
theorem artifactBoundOracle (hidden : Hidden) (oracle : InternalOracle)
    (pairs : LabelPairs) :
    (scheme.garbleBytes hidden oracle pairs).size ≤ claimedBytes := by
  change (CosetFamilyArtifact.encode
    (garbleWithOracle hidden oracle pairs)).size ≤ _
  rw [garbleWithOracle_eq]
  exact artifactBound hidden (randomnessFromOracle hidden oracle) (coinsFromOracle oracle) pairs


end GarblingPrize.Submission.CosetScheme
