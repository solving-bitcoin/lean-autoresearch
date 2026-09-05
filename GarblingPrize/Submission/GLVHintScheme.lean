import GarblingPrize.Submission.GLVHintFamilyArtifact
import GarblingPrize.Submission.GLVHintProjectiveMapRuntime
import GarblingPrize.Submission.GLVCompactPrivacy

namespace GarblingPrize.Submission.GLVHintScheme

/-! Exact one-hint affine tables in the norm-seven GLV construction.
The group and scalar mathematics are reused unchanged. Each of the 91 maps
contains eleven 8160-byte tables, for exactly 8,168,160 bytes. -/

open GarblingPrize.Protected
open EisensteinRadix GLVCompactScheme

abbrev Artifact := GLVHintFamilyArtifact.Artifact 91
abbrev Coin := HintAffineTable.Coin
abbrev Coins := BitIndex → Purpose → Coin

local instance concreteGroup : AddCommGroup BN254.G1 := BN254.bn254.addCommGroup
local instance profileGroup : AddCommGroup Profile.G1 := concreteGroup

set_option exponentiation.threshold 4096 in
private theorem coinModulus_fits : 4 * BinaryFieldHint.modulus ≤ 2 ^ 3072 := by
  have h : 4 * BinaryFieldHint.modulus ≤ 2 ^ 257 := by
    norm_num [BinaryFieldHint.modulus, baseFieldModulus]
  exact h.trans (Nat.pow_le_pow_right (by decide) (by decide))

def coinModulus : SamplingModulus :=
  ⟨4 * BinaryFieldHint.modulus, by
    have := HintAffineTable.modulus_positive
    omega, coinModulus_fits⟩

def coinPurpose (wire : BitIndex) (purpose : Purpose) : Purpose :=
  512 * purpose + wire.val

def coinsFromOracle (oracle : InternalOracle) : Coins :=
  fun wire purpose => oracle coinModulus (coinPurpose wire purpose)

def tableCoins (coins : Coins) (index : Fin 91)
    (kind : GLVProjectiveMap.TableKind) : HintAffineTable.RowIndex → Coin :=
  fun row => coins (GLVCompactPrivacy.tableWire kind row)
    (GLVHintProjectiveMap.purpose index.val kind)

def garble (hidden : Hidden) (randomness : Randomness hidden)
    (coins : Coins) (pairs : LabelPairs) : Artifact where
  maps := fun index => GLVHintProjectiveMap.garble index.val
    (xPairs pairs) (yPairs pairs)
    (mapHidden hidden randomness.offsets randomness.randomizers randomness.chainMasks index)
    (tableCoins coins index)

@[simp] theorem garble_map (hidden : Hidden) (randomness : Randomness hidden)
    (coins : Coins) (pairs : LabelPairs) (index : Fin 91) :
    (garble hidden randomness coins pairs).maps index =
      GLVHintProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
        (mapHidden hidden randomness.offsets randomness.randomizers randomness.chainMasks index)
        (tableCoins coins index) := rfl

def materializeTable (table : HintAffineTable.Table) : HintAffineTable.Table := table

@[simp] theorem materializeTable_eq (table : HintAffineTable.Table) :
    materializeTable table = table := rfl

def garbleWithOracle (hidden : Hidden) (oracle : InternalOracle)
    (pairs : LabelPairs) : Artifact :=
  let randomness := randomnessFromOracle hidden oracle
  let maps := materializedMapHiddenFamily hidden randomness.offsets
    randomness.randomizers randomness.chainMasks
  { maps := fun index =>
      { tables := fun kind =>
          let coins := Vector.ofFn (tableCoins (coinsFromOracle oracle) index kind)
          materializeTable (HintAffineTable.garble
            (GLVHintProjectiveMap.purpose index.val kind)
            (GLVHintProjectiveMap.pairsFor (xPairs pairs) (yPairs pairs) kind)
            ((maps index).params kind) (fun row => coins[row.val])) } }

theorem garbleWithOracle_eq (hidden : Hidden) (oracle : InternalOracle)
    (pairs : LabelPairs) :
    garbleWithOracle hidden oracle pairs =
      garble hidden (randomnessFromOracle hidden oracle) (coinsFromOracle oracle) pairs := by
  apply GLVHintFamilyArtifact.Artifact.ext
  funext index
  apply GLVHintProjectiveMap.Artifact.ext
  funext kind
  simp [garbleWithOracle, garble, GLVHintProjectiveMap.garble]

def evaluateMap (index : Fin 91) (artifact : GLVHintProjectiveMap.Artifact)
    (input : Input) (labels : ActiveLabels) : Except EvalError Point :=
  GLVHintProjectiveMapRuntime.evaluate index.val artifact
    (input.x.val : Word) (input.y.val : Word)
    (xBits input) (yBits input) (xLabels labels) (yLabels labels)

def evaluateMaps (artifact : Artifact) (input : Input)
    (labels : ActiveLabels) : List (Fin 91) → Except EvalError (List Point)
  | [] => .ok []
  | index :: tail => do
      let point ← evaluateMap index (artifact.maps index) input labels
      let points ← evaluateMaps artifact input labels tail
      pure (point :: points)

def evaluate (artifact : Artifact) (input : Input)
    (labels : ActiveLabels) : Except EvalError Profile.Output := do
  let points ← evaluateMaps artifact input labels (List.finRange 91)
  let result ← RuntimeG1.recomposeAlpha points
  pure (show Profile.Output from RuntimeG1.toOutput result)

theorem evaluateMap_projectiveGarble (offset : BN254.G1) (digit : Digit)
    (randomizer : Wordˣ) (chainMasks : GLVProjectiveMap.ChainMasks)
    (tableMasks : GLVProjectiveMap.TableKind → HintAffineTable.RowIndex → Coin)
    (pairs : LabelPairs) (input : Input) (index : Fin 91) :
    ∃ result : Point,
      evaluateMap index
          (GLVHintProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
            (localHidden offset digit randomizer chainMasks) tableMasks)
          input
          (activeLabels pairs input) = Except.ok result ∧
        RuntimeG1.toPoint result =
          EisensteinFullWidth.mapOutput offset digit (-inputG1 input) := by
  have hlabelsX := active_xLabels pairs input
  have hlabelsY := active_yLabels pairs input
  have hprojective := polynomial_randomizedCoefficients
    offset digit randomizer input
  have hvalid := rawMap_valid offset digit input
  obtain ⟨result, hnormalize, hresult⟩ :=
    RuntimeG1.normalize_randomize_of_valid
      (rawMap offset digit input) hvalid randomizer
  refine ⟨result, ?_, ?_⟩
  · unfold evaluateMap
    rw [hlabelsX, hlabelsY, ← decodeBits_xBits, ← decodeBits_yBits]
    calc
      GLVHintProjectiveMapRuntime.evaluate index.val
          (GLVHintProjectiveMap.garble index.val (xPairs pairs) (yPairs pairs)
            (localHidden offset digit randomizer chainMasks) tableMasks)
          (IdealAffineTable.decodeBits (xBits input))
          (IdealAffineTable.decodeBits (yBits input))
          (xBits input) (yBits input)
          (fun i => xPairs pairs i (xBits input i))
          (fun i => yPairs pairs i (yBits input i)) =
          GLVHintProjectiveMapRuntime.normalizeCoordinates
            (ProjectiveMap.polynomial
              (localHidden offset digit randomizer chainMasks).coefficients
              (IdealAffineTable.decodeBits (xBits input))
              (IdealAffineTable.decodeBits (yBits input))) :=
            GLVHintProjectiveMapRuntime.evaluate_garble index.val
              (xPairs pairs) (yPairs pairs)
              (localHidden offset digit randomizer chainMasks) tableMasks
              (xBits input) (yBits input)
              (by
                rw [decodeBits_xBits, decodeBits_yBits]
                change ((input.y.val : Word) ^ 2 =
                  (input.x.val : Word) ^ 3 + 3)
                exact input.onCurve)
      _ = Except.ok result := by
        rw [decodeBits_xBits, decodeBits_yBits]
        unfold GLVHintProjectiveMapRuntime.normalizeCoordinates
        rw [show (localHidden offset digit randomizer chainMasks).coefficients =
            randomizedCoefficients offset digit randomizer by rfl,
          hprojective]
        exact hnormalize
  · rw [hresult, decode_rawMap, mapOutput_eq]

theorem evaluateMap_garble (hidden : Hidden) (randomness : Randomness hidden)
    (coins : Coins) (pairs : LabelPairs) (input : Input) (index : Fin 91) :
    ∃ result : Point,
      evaluateMap index ((garble hidden randomness coins pairs).maps index) input
          (activeLabels pairs input) = Except.ok result ∧
        RuntimeG1.toPoint result =
          EisensteinFullWidth.mapOutput (offsetAt randomness.offsets index)
            (digitAt hidden index) (-inputG1 input) := by
  rw [garble_map]
  exact evaluateMap_projectiveGarble
    (offsetAt randomness.offsets index) (digitAt hidden index)
    (randomness.randomizers index) (randomness.chainMasks index)
    (tableCoins coins index) pairs input index

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

def encodeArtifact : Artifact → ByteArray := GLVHintFamilyArtifact.encode

/-- Native execution may build the independent map encodings concurrently.
The logical scheme and all privacy proofs continue to see the canonical
sequential encoder. -/
def encodeArtifactParallel : Artifact → ByteArray :=
  GLVHintFamilyArtifact.encodeParallel

@[csimp] theorem encodeArtifact_eq_parallel :
    encodeArtifact = encodeArtifactParallel := by
  funext artifact
  simp [encodeArtifact, encodeArtifactParallel]

def decodeArtifact (bytes : ByteArray) : Except DecodeError Artifact :=
  match GLVHintFamilyArtifact.decode 91 bytes with
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
    rw [GLVHintFamilyArtifact.decode_encode]
  · intro bytes artifact hdecode
    unfold decodeArtifact at hdecode
    cases hfamily : GLVHintFamilyArtifact.decode 91 bytes with
    | error error =>
        cases error <;> simp [hfamily] at hdecode
    | ok decoded =>
        have hdecoded : decoded = artifact := by simpa [hfamily] using hdecode
        subst decoded
        exact GLVHintFamilyArtifact.encode_decode hfamily

theorem correct : Correct scheme := by
  apply Scheme.correct_ofFunctions Artifact garbleWithOracle evaluate
    encodeArtifact decodeArtifact codec
  intro hidden oracle pairs input
  rw [garbleWithOracle_eq]
  exact artifactCorrect hidden (randomnessFromOracle hidden oracle) (coinsFromOracle oracle) pairs input

def claimedBytes : Nat := 8168160

set_option maxRecDepth 4096 in
theorem artifactBound (hidden : Hidden) (randomness : Randomness hidden)
    (coins : Coins) (pairs : LabelPairs) :
    (GLVHintFamilyArtifact.encode (garble hidden randomness coins pairs)).size ≤
      claimedBytes := by
  rw [GLVHintFamilyArtifact.encode_size, GLVHintFamilyArtifact.ninetyOne_byteCount]
  rfl

set_option maxRecDepth 4096 in
theorem artifactBoundOracle (hidden : Hidden) (oracle : InternalOracle)
    (pairs : LabelPairs) :
    (scheme.garbleBytes hidden oracle pairs).size ≤ claimedBytes := by
  change (GLVHintFamilyArtifact.encode
    (garbleWithOracle hidden oracle pairs)).size ≤ _
  rw [garbleWithOracle_eq]
  exact artifactBound hidden (randomnessFromOracle hidden oracle) (coinsFromOracle oracle) pairs


end GarblingPrize.Submission.GLVHintScheme
