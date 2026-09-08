import G1Release.Submission.SchemeEval

namespace G1Release.Submission.Scheme
open SecretRelease
open G1Release.Protected
open GarblingPrize.Protected

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem evaluate_garble (hash : Hash) (hidden : Hidden)
    (keys : Fin 512 → Pair) (input : Input) :
    evaluate hash (garble hash hidden keys) input
        (challenge.inputs.reveal hash keys input) =
      some (encodeOutput (reference hidden input)) := by
  have hsize := reveal_size hash keys input
  obtain ⟨points, hpoints, hpointsValue⟩ :=
    evaluateMaps_garble hash hidden keys input (List.finRange 161)
  obtain ⟨result, hresult, hresultValue⟩ := RuntimeG1.recompose_correct points
  unfold evaluate
  rw [size_bne_false hsize]
  have hfalse : ¬ (false = true) := by decide
  rw [if_neg hfalse]
  have hpoints' :
      evaluateMaps hash (garble hash hidden keys) input
          (challenge.inputs.reveal hash keys input) (List.finRange 161) =
        some points := hpoints
  erw [hpoints']
  change (match RuntimeG1.recompose points with
      | .error _ => none
      | .ok result => some (encodeOutput (RuntimeG1.toOutput result))) =
    some (encodeOutput (reference hidden input))
  rw [hresult]
  apply congrArg some
  apply congrArg encodeOutput
  change RuntimeG1.toOutput result =
    BN254.CanonicalOutput.ofPoint
      (hidden.1.toPoint + hidden.2.val • inputG1 input)
  unfold RuntimeG1.toOutput
  apply congrArg BN254.CanonicalOutput.ofPoint
  rw [hresultValue, hpointsValue, honest_recompose hidden
    (OffsetFamily.canonical hidden) input]
  rfl

end G1Release.Submission.Scheme
