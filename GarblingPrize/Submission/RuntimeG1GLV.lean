import GarblingPrize.Submission.EisensteinFullWidth
import GarblingPrize.Submission.RuntimeG1

namespace GarblingPrize.Submission.RuntimeG1

open GarblingPrize.Protected

local instance concreteGroup : AddCommGroup BN254.G1 :=
  BN254.bn254.addCommGroup

/-- The native `3 + phi` Horner loop refines the exact norm-seven group
recomposition. -/
theorem recomposeAlpha_correct (points : List Point) :
    ∃ result : Point,
      recomposeAlpha points = .ok result ∧
        toPoint result =
          EisensteinFullWidth.recompose (points.map toPoint) := by
  induction points with
  | nil => exact ⟨infinity, rfl, rfl⟩
  | cons head tail ih =>
      obtain ⟨tailResult, htail, htailPoint⟩ := ih
      obtain ⟨scaled, hscaled, hscaledPoint⟩ := alpha_correct tailResult
      obtain ⟨result, hresult, hresultPoint⟩ := add_correct head scaled
      refine ⟨result, ?_, ?_⟩
      · unfold recomposeAlpha
        rw [htail]
        change (do
          let scaled ← alpha tailResult
          add head scaled) = .ok result
        rw [hscaled]
        exact hresult
      · rw [hresultPoint, hscaledPoint, htailPoint]
        simp only [List.map_cons, EisensteinFullWidth.recompose_cons]
        exact congrArg (toPoint head + ·)
          (EisensteinFullWidth.alphaPoint_eq_three_add_phi
            (EisensteinFullWidth.recompose
              (List.map toPoint tail))).symm

end GarblingPrize.Submission.RuntimeG1
