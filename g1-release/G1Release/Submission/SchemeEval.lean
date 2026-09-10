import G1Release.Submission.SchemeCorrect

namespace G1Release.Submission.Scheme
open SecretRelease
open G1Release.Protected
open G1Release.Math

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem evaluateOne_eq (hash : Hash) (artifact : Artifact) (input : Input)
    (active : ByteArray) (index : Fin 161) :
    evaluateOne hash artifact input active index =
      (mapAt artifact index).bind fun m =>
        evaluateMap hash index m input active :=
  rfl

theorem evaluateOne_garble (hash : Hash) (hidden : Hidden)
    (keys : Fin 512 → Pair) (input : Input) (index : Fin 161) :
    ∃ result : Point,
      evaluateOne hash (garble hash hidden keys) input
          (challenge.inputs.reveal hash keys input) index = some result ∧
        RuntimeG1.toPoint result =
          offsetAt (OffsetFamily.canonical hidden) index +
            (digitAt hidden index).value • inputG1 input := by
  obtain ⟨result, hresult, hvalue⟩ :=
    evaluateMap_garbleMaps hash hidden keys input index
  refine ⟨result, ?_, hvalue⟩
  rw [evaluateOne_eq]
  erw [mapAt_garble, Option.bind_some, hresult]

theorem evaluateMaps_garble (hash : Hash) (hidden : Hidden)
    (keys : Fin 512 → Pair) (input : Input) (indices : List (Fin 161)) :
    ∃ results : List Point,
      evaluateMaps hash (garble hash hidden keys) input
          (challenge.inputs.reveal hash keys input) indices = some results ∧
        results.map RuntimeG1.toPoint =
          indices.map fun index =>
            offsetAt (OffsetFamily.canonical hidden) index +
              (digitAt hidden index).value • inputG1 input := by
  induction indices with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons index indices ih =>
      obtain ⟨point, hpoint, hpointValue⟩ :=
        evaluateOne_garble hash hidden keys input index
      obtain ⟨points, hpoints, hpointsValue⟩ := ih
      refine ⟨point :: points, ?eval, ?pts⟩
      · unfold evaluateMaps at hpoints ⊢
        rw [List.mapM_cons]
        erw [hpoint]
        have hpoints' :
            List.mapM (evaluateOne hash (garble hash hidden keys) input
                (challenge.inputs.reveal hash keys input)) indices =
              some points := hpoints
        erw [hpoints']
        rfl
      · simp [hpointValue, hpointsValue]

theorem size_bne_false {n : Nat} (h : n = 16384) : (n != 16384) = false := by
  simp [h]

end G1Release.Submission.Scheme
