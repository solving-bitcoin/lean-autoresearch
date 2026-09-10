import G1Release.Submission.EisensteinFullWidth
import G1Release.Submission.RuntimeG1

namespace G1Release.Submission.RuntimeG1

open G1Release.Math

local instance concreteGroup : AddCommGroup BN254.G1 :=
  inferInstance

/-! ## Native norm-seven GLV recomposition -/

/-- The checked coordinate endomorphism `(x,y) |-> (beta*x,y)` on the
proof-carrying runtime point. -/
def endomorphism : Point → Point
  | ⟨none, _⟩ => infinity
  | ⟨some point, hpoint⟩ =>
      ofAffine ⟨G1Endomorphism.beta * point.x, point.y⟩ (by
        change
          (G1Endomorphism.beta * point.x) ^ 3 + 3 = point.y ^ 2
        change point.x ^ 3 + 3 = point.y ^ 2 at hpoint
        rw [mul_pow, G1Endomorphism.beta_pow_three, one_mul]
        exact hpoint)

theorem toPoint_endomorphism (point : Point) :
    toPoint (endomorphism point) =
      G1Endomorphism.phi (toPoint point) := by
  rcases point with ⟨point, hpoint⟩
  cases point with
  | none => rfl
  | some point =>
      unfold endomorphism toPoint ofAffine G1Endomorphism.phi
      congr

/-- One native Horner multiplication by `3 + phi`. -/
def alpha (point : Point) : Except EvalError Point := do
  let tripled ← triple point
  add tripled (endomorphism point)

theorem alpha_correct (point : Point) :
    ∃ result : Point,
      alpha point = .ok result ∧
        toPoint result =
          3 • toPoint point + G1Endomorphism.phi (toPoint point) := by
  obtain ⟨tripled, htripled, htripledPoint⟩ := triple_correct point
  obtain ⟨result, hresult, hresultPoint⟩ :=
    add_correct tripled (endomorphism point)
  refine ⟨result, ?_, ?_⟩
  · unfold alpha
    rw [htripled]
    exact hresult
  · rw [hresultPoint, htripledPoint, toPoint_endomorphism]

/-- Little-endian norm-seven recomposition used by the GLV evaluator. -/
def recomposeAlpha : List Point → Except EvalError Point
  | [] => .ok infinity
  | head :: tail => do
      let tailResult ← recomposeAlpha tail
      let scaled ← alpha tailResult
      add head scaled


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

end G1Release.Submission.RuntimeG1
