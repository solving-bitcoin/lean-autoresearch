import G1Release.Submission.Randomized

namespace G1Release.Submission.Randomized
open GarblingPrize.Protected G1Release.Protected SecretRelease

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem evaluateMap_garble (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (index : Fin 161) :
    ∃ result : RuntimeG1.Point,
      Scheme.evaluateMap hash index (maps hash hidden random keys index) input
          (challenge.inputs.reveal hash keys input) = some result ∧
        RuntimeG1.toPoint result =
          Scheme.offsetAt random.offsets index +
            (Scheme.digitAt hidden index).value • Scheme.inputG1 input := by
  let offset := Scheme.offsetAt random.offsets index
  let digit := Scheme.digitAt hidden index
  let scale := random.scales index
  obtain ⟨result, hnormalize, hvalue⟩ :=
    RuntimeG1.normalize_randomize_of_valid (Scheme.rawMap offset digit input)
      (Scheme.rawMap_valid offset digit input) scale
  refine ⟨result, ?_, ?_⟩
  · have hmap := ProjectiveMap.evaluate_garble hash index.val
      (Scheme.xPairs keys) (Scheme.yPairs keys)
      (mapHidden hidden random.offsets random.scales random.chains index)
      (random.masks index) (Scheme.xBits input) (Scheme.yBits input)
      (Scheme.onCurve_decodeBits input)
      (coefficients_xX offset digit scale) (coefficients_zXX offset digit scale)
    rw [Scheme.decodeBits_xBits, Scheme.decodeBits_yBits] at hmap
    change Scheme.finish (ProjectiveMap.evaluate hash index.val
      (maps hash hidden random keys index)
      (input.val.1.val : Word) (input.val.2.val : Word)
      (Scheme.xBits input) (Scheme.yBits input)
      (Scheme.evalXLabels (challenge.inputs.reveal hash keys input))
      (Scheme.evalYLabels (challenge.inputs.reveal hash keys input))) = some result
    rw [Scheme.evalXLabels_reveal_eq, Scheme.evalYLabels_reveal_eq]
    change Scheme.finish (ProjectiveMap.evaluate hash index.val
      (maps hash hidden random keys index)
      (input.val.1.val : Word) (input.val.2.val : Word)
      (Scheme.xBits input) (Scheme.yBits input)
      (fun i => Scheme.xPairs keys i (Scheme.xBits input i))
      (fun i => Scheme.yPairs keys i (Scheme.yBits input i))) = some result
    rw [show maps hash hidden random keys index =
        ProjectiveMap.garble hash index.val (Scheme.xPairs keys) (Scheme.yPairs keys)
          (mapHidden hidden random.offsets random.scales random.chains index)
          (random.masks index) from rfl, hmap]
    change Scheme.finish (some (ProjectiveMap.polynomial
      (coefficients offset digit scale) (input.val.1.val : Word) (input.val.2.val : Word))) = _
    rw [polynomial_coefficients, Scheme.finish_ofHomogeneous, hnormalize]
  · rw [hvalue, Scheme.decode_rawMap]

theorem evaluateOne_garble (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (index : Fin 161) :
    ∃ result : RuntimeG1.Point,
      Scheme.evaluateOne hash (garble hash hidden random keys) input
          (challenge.inputs.reveal hash keys input) index = some result ∧
        RuntimeG1.toPoint result = Scheme.offsetAt random.offsets index +
          (Scheme.digitAt hidden index).value • Scheme.inputG1 input := by
  obtain ⟨result, hresult, hvalue⟩ := evaluateMap_garble hash hidden random keys input index
  refine ⟨result, ?_, hvalue⟩
  rw [Scheme.evaluateOne_eq]
  erw [mapAt_garble, Option.bind_some, hresult]

theorem evaluateMaps_garble (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (indices : List (Fin 161)) :
    ∃ results : List RuntimeG1.Point,
      Scheme.evaluateMaps hash (garble hash hidden random keys) input
          (challenge.inputs.reveal hash keys input) indices = some results ∧
        results.map RuntimeG1.toPoint = indices.map fun index =>
          Scheme.offsetAt random.offsets index +
            (Scheme.digitAt hidden index).value • Scheme.inputG1 input := by
  induction indices with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons index indices ih =>
    obtain ⟨point, hpoint, hpointValue⟩ := evaluateOne_garble hash hidden random keys input index
    obtain ⟨points, hpoints, hpointsValue⟩ := ih
    refine ⟨point :: points, ?_, ?_⟩
    · unfold Scheme.evaluateMaps at hpoints ⊢
      rw [List.mapM_cons]
      erw [hpoint]
      have hpoints' : List.mapM (Scheme.evaluateOne hash (garble hash hidden random keys)
          input (challenge.inputs.reveal hash keys input)) indices = some points := hpoints
      erw [hpoints']
      rfl
    · simp [hpointValue, hpointsValue]

theorem evaluate_garble (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) :
    Scheme.evaluate hash (garble hash hidden random keys) input
        (challenge.inputs.reveal hash keys input) =
      some (encodeOutput (reference hidden input)) := by
  obtain ⟨points, hpoints, hpointsValue⟩ :=
    evaluateMaps_garble hash hidden random keys input (List.finRange 161)
  obtain ⟨result, hresult, hresultValue⟩ := RuntimeG1.recompose_correct points
  unfold Scheme.evaluate
  rw [Scheme.size_bne_false (Scheme.reveal_size hash keys input)]
  rw [if_neg (by decide : ¬ (false = true))]
  erw [hpoints]
  change (match RuntimeG1.recompose points with
    | .error _ => none
    | .ok result => some (encodeOutput (RuntimeG1.toOutput result))) = _
  rw [hresult]
  apply congrArg some
  apply congrArg encodeOutput
  change RuntimeG1.toOutput result = BN254.CanonicalOutput.ofPoint
    (hidden.1.toPoint + hidden.2.val • Scheme.inputG1 input)
  unfold RuntimeG1.toOutput
  apply congrArg BN254.CanonicalOutput.ofPoint
  rw [hresultValue, hpointsValue, Scheme.honest_recompose hidden random.offsets input]
  rfl

/-- Exact serialized correctness for every byte-tape sampler. No assumption
on uniformity, oracle freshness, or sampling success is used here. -/
theorem correct (n : Nat) (sample : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden) :
    Correct (scheme n sample) := by
  intro hash coins hidden keys outputs input
  delta SecretRelease.Scheme.evaluateBytes SecretRelease.Scheme.garbleBytes
  erw [scheme_garble, scheme_encode, scheme_decode, Scheme.decode_encode]
  erw [Option.bind_some, scheme_evaluate, evaluate_garble]
  rfl

end G1Release.Submission.Randomized
