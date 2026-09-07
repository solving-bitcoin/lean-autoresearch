import G1Release.Submission.CosetScheme

namespace G1Release.Submission.CosetScheme
open SecretRelease G1Release.Protected GarblingPrize.Protected
open GLVDigits CosetCoordinates FourAffineQuotient
open Scheme (runtimeOfGroup toPoint_runtimeOfGroup inputG1 xBits yBits)
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem evaluate_openings (hash : Hash) (keys : Keys) (input : Input)
    (index : Fin 91) (base : Base K) (state : State K) (coins : CosetHintMap.Coins) :
    CosetHintMap.evaluate index.val
        (CosetHintMap.garble index.val (xPads hash keys) (yPads hash keys) base state coins)
        (xBits input) (yBits input)
        (pads hash (Scheme.evalXLabels (challenge.inputs.reveal hash keys input)))
        (pads hash (Scheme.evalYLabels (challenge.inputs.reveal hash keys input))) =
      some (opened base state (C (input.val.1.val : Word)) (C (input.val.2.val : Word))) := by
  rw [Scheme.evalXLabels_reveal_eq, Scheme.evalYLabels_reveal_eq]
  have hx : pads hash (Scheme.xLabels keys input) = fun i => xPads hash keys i (xBits input i) := rfl
  have hy : pads hash (Scheme.yLabels keys input) = fun i => yPads hash keys i (yBits input i) := rfl
  rw [hx, hy]
  erw [CosetHintMap.evaluate_garble]
  change some (opened base state (C (AffineTable.decodeBits (xBits input)))
    (C (AffineTable.decodeBits (yBits input)))) = _
  rw [Scheme.decodeBits_xBits, Scheme.decodeBits_yBits]

theorem evaluateMap_garble (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (coins : Coins) (keys : Keys) (input : Input) (index : Fin 91) :
    evaluateMap hash index ((garble hash hidden random coins keys).maps index) input
        (challenge.inputs.reveal hash keys input) =
      some (runtimeOfGroup (EisensteinFullWidth.mapOutput (offsetAt random.offsets index)
        (digitAt hidden index) (-inputG1 input))) := by
  rw [garble_maps]
  unfold evaluateMap
  rw [evaluate_openings]
  exact CosetGLV.decode_openings _ _ input (random.states index)

theorem evaluateMaps_garble (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (coins : Coins) (keys : Keys) (input : Input) (indices : List (Fin 91)) :
    evaluateMaps hash (garble hash hidden random coins keys) input
        (challenge.inputs.reveal hash keys input) indices =
      some (indices.map fun index => runtimeOfGroup
        (EisensteinFullWidth.mapOutput (offsetAt random.offsets index)
          (digitAt hidden index) (-inputG1 input))) := by
  induction indices with
  | nil => rfl
  | cons index indices ih =>
      rw [evaluateMaps, evaluateMap_garble, ih]
      rfl

theorem honest_recompose (hidden : Private) (random : Randomness hidden) (input : Input) :
    EisensteinFullWidth.recompose ((List.finRange 91).map fun index =>
      EisensteinFullWidth.mapOutput (offsetAt random.offsets index)
        (digitAt hidden index) (-inputG1 input)) =
      hidden.1.toPoint + hidden.2.val • inputG1 input := by
  rw [GLVDigits.fullMapOutputs]
  change EisensteinFullWidth.outputList random.offsets.values
    (GLVOffsetFamily.digits hidden) (-inputG1 input) = _
  have h := EisensteinFullWidth.output_scalar random.offsets.values hidden.2
    (-inputG1 input) random.offsets.length_eq
  unfold GLVOffsetFamily.digits
  rw [h, random.offsets.total_eq, EisensteinFullWidth.point_nsmul_neg]
  change hidden.1.toPoint - -(hidden.2.val • inputG1 input) = _
  abel

theorem evaluate_garble (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (coins : Coins) (keys : Keys) (input : Input) :
    evaluate hash (garble hash hidden random coins keys) input
        (challenge.inputs.reveal hash keys input) =
      some (encodeOutput (reference hidden input)) := by
  let points := (List.finRange 91).map fun index => runtimeOfGroup
    (EisensteinFullWidth.mapOutput (offsetAt random.offsets index)
      (digitAt hidden index) (-inputG1 input))
  obtain ⟨result, hresult, hvalue⟩ := RuntimeG1.recomposeAlpha_correct points
  unfold evaluate
  rw [Scheme.reveal_size]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [evaluateMaps_garble]
  change (match RuntimeG1.recomposeAlpha points with
    | .error _ => none
    | .ok result => some (encodeOutput (RuntimeG1.toOutput result))) = _
  rw [hresult]
  apply congrArg some
  apply congrArg encodeOutput
  change RuntimeG1.toOutput result = BN254.CanonicalOutput.ofPoint
    (hidden.1.toPoint + hidden.2.val • inputG1 input)
  unfold RuntimeG1.toOutput
  apply congrArg BN254.CanonicalOutput.ofPoint
  rw [hvalue]
  have hp : points.map RuntimeG1.toPoint = (List.finRange 91).map fun index =>
      EisensteinFullWidth.mapOutput (offsetAt random.offsets index)
        (digitAt hidden index) (-inputG1 input) := by
    simp only [points, List.map_map, Function.comp_def, toPoint_runtimeOfGroup]
  rw [hp, honest_recompose]

theorem correct (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Private) → Randomness hidden × Coins) :
    Correct (scheme n sample) := by
  intro hash coins hidden keys outputs input
  delta SecretRelease.Scheme.evaluateBytes SecretRelease.Scheme.garbleBytes
  erw [scheme_garble, scheme_encode, scheme_decode, decode_encode]
  erw [Option.bind_some, scheme_evaluate, evaluate_garble]
  rfl

end G1Release.Submission.CosetScheme
