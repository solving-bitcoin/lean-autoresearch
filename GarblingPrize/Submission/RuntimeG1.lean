import GarblingPrize.Submission.FormulaSemantics
import GarblingPrize.Submission.G1Endomorphism
import GarblingPrize.Submission.TernaryFullWidth

namespace GarblingPrize.Submission.RuntimeG1

open GarblingPrize.Protected
open WeierstrassCurve
open WeierstrassCurve.Jacobian

abbrev Word := BN254.Fq
abbrev Affine := HomogeneousRCBG1GroupLaw.Affine
abbrev RawPoint := HomogeneousRCBG1GroupLaw.Homogeneous

/-- A proof-carrying two-case point used by the native evaluator.  Proof
fields erase during code generation; the data are just infinity or two field
elements. -/
def Point :=
  { point : Option Affine // HomogeneousRCBG1GroupLaw.InputOnCurve point }

def infinity : Point := ⟨none, trivial⟩

def ofAffine (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) : Point :=
  ⟨some point, hpoint⟩

def encode (point : Point) : RawPoint :=
  HomogeneousRCBG1GroupLaw.encode point.1

/-- Executable normalization with an explicit curve check.  The check makes
the function total even on hostile decoded artifacts. -/
def normalize (point : RawPoint) : Except EvalError Point :=
  if _hz : point.z = 0 then
    .ok infinity
  else
    let zInverse := point.z⁻¹
    let affine : Affine := ⟨point.x * zInverse, point.y * zInverse⟩
    if hcurve : HomogeneousRCBG1GroupLaw.AffineOnCurve affine then
      .ok (ofAffine affine hcurve)
    else
      .error .internalFailure

/-- Semantic embedding into the protected affine group. -/
def toPoint (point : Point) : BN254.G1 :=
  match point with
  | ⟨none, _⟩ => 0
  | ⟨some affine, hcurve⟩ =>
      .some affine.x affine.y
        (HomogeneousRCBG1GroupLaw.affine_nonsingular affine hcurve)

/-- Canonical protected output carrier. -/
def toOutput (point : Point) : BN254.CanonicalOutput :=
  BN254.CanonicalOutput.ofPoint (toPoint point)

theorem toPoint_negAffine (point : Affine)
    (hpoint : HomogeneousRCBG1GroupLaw.AffineOnCurve point) :
    toPoint
        (ofAffine (HomogeneousRCBG1GroupLaw.negAffine point)
          (HomogeneousRCBG1GroupLaw.negAffine_onCurve point hpoint)) =
      -toPoint (ofAffine point hpoint) := by
  unfold toPoint ofAffine
  rw [WeierstrassCurve.Affine.Point.neg_some]
  simp [BN254.curve,
    HomogeneousRCBG1GroupLaw.negAffine,
    WeierstrassCurve.Affine.negY]
  congr

@[simp] theorem output_toPoint (point : Point) :
    BN254.CanonicalOutput.toPoint (toOutput point) = toPoint point := by
  exact BN254.CanonicalOutput.toPoint_ofPoint (toPoint point)

theorem normalized_onCurve (point : RawPoint)
    (hvalid : BN254.curve.toJacobian.Nonsingular
      (HomogeneousRCBG1GroupLaw.toJacobian point))
    (hz : point.z ≠ 0) :
    HomogeneousRCBG1GroupLaw.AffineOnCurve
      ⟨point.x / point.z, point.y / point.z⟩ := by
  have hzJacobian :
      HomogeneousRCBG1GroupLaw.toJacobian point (2 : Fin 3) ≠ 0 := by
    simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]
  have hns :=
    (BN254.curve.toJacobian.nonsingular_of_Z_ne_zero hzJacobian).mp hvalid
  have hx :
      (HomogeneousRCBG1GroupLaw.toJacobian point (0 : Fin 3) /
          HomogeneousRCBG1GroupLaw.toJacobian point (2 : Fin 3) ^ 2) =
        point.x / point.z := by
    simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]
    field_simp
  have hy :
      (HomogeneousRCBG1GroupLaw.toJacobian point (1 : Fin 3) /
          HomogeneousRCBG1GroupLaw.toJacobian point (2 : Fin 3) ^ 3) =
        point.y / point.z := by
    simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]
    field_simp
  rw [hx, hy] at hns
  have hequation :=
    (BN254.curve.toAffine.equation_iff_nonsingular_of_Δ_ne_zero
      BN254.discriminant_ne_zero).mpr hns
  rw [WeierstrassCurve.Affine.equation_iff] at hequation
  simpa [HomogeneousRCBG1GroupLaw.AffineOnCurve, BN254.curve] using
    hequation.symm

theorem normalize_of_valid (point : RawPoint)
    (hvalid : BN254.curve.toJacobian.Nonsingular
      (HomogeneousRCBG1GroupLaw.toJacobian point)) :
    ∃ normalized : Point,
      normalize point = .ok normalized ∧
        toPoint normalized = FormulaSemantics.Law.decode point := by
  by_cases hz : point.z = 0
  · refine ⟨infinity, ?_, ?_⟩
    · simp [normalize, hz]
    · unfold toPoint FormulaSemantics.Law.decode
      rw [show HomogeneousRCBG1GroupLaw.toJacobian point =
          ![(1 : Word), 1, 0] by
        simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]]
      exact WeierstrassCurve.Jacobian.Point.toAffine_zero.symm
  · let affine : Affine := ⟨point.x * point.z⁻¹, point.y * point.z⁻¹⟩
    have hcurve : HomogeneousRCBG1GroupLaw.AffineOnCurve affine := by
      simpa [affine, div_eq_mul_inv] using
        normalized_onCurve point hvalid hz
    refine ⟨ofAffine affine hcurve, ?_, ?_⟩
    · unfold normalize
      rw [dif_neg hz]
      rw [dif_pos (show HomogeneousRCBG1GroupLaw.AffineOnCurve
        { x := point.x * point.z⁻¹, y := point.y * point.z⁻¹ } from hcurve)]
    · unfold toPoint FormulaSemantics.Law.decode
      have hzJacobian :
          HomogeneousRCBG1GroupLaw.toJacobian point (2 : Fin 3) ≠ 0 := by
        simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]
      rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero
        hvalid hzJacobian]
      simp [ofAffine, affine,
        HomogeneousRCBG1GroupLaw.toJacobian, hz, div_eq_mul_inv]
      constructor <;> field_simp

theorem normalize_randomize_of_valid (point : RawPoint)
    (hvalid : BN254.curve.toJacobian.Nonsingular
      (HomogeneousRCBG1GroupLaw.toJacobian point)) (factor : Wordˣ) :
    ∃ normalized : Point,
      normalize (HomogeneousRCB.randomize (factor : Word) point) =
          .ok normalized ∧
        toPoint normalized = FormulaSemantics.Law.decode point := by
  let randomized := HomogeneousRCB.randomize (factor : Word) point
  by_cases hz : point.z = 0
  · have hzRandomized : randomized.z = 0 := by
      simp [randomized, HomogeneousRCB.randomize, hz]
    refine ⟨infinity, ?_, ?_⟩
    · change normalize randomized = .ok infinity
      simp [normalize, hzRandomized]
    · unfold toPoint FormulaSemantics.Law.decode
      rw [show HomogeneousRCBG1GroupLaw.toJacobian point =
          ![(1 : Word), 1, 0] by
        simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]]
      exact WeierstrassCurve.Jacobian.Point.toAffine_zero.symm
  · have hfactor : (factor : Word) ≠ 0 := Units.ne_zero factor
    have hzRandomized : randomized.z ≠ 0 := by
      simp [randomized, HomogeneousRCB.randomize, hfactor, hz]
    let affine : Affine :=
      ⟨randomized.x * randomized.z⁻¹,
        randomized.y * randomized.z⁻¹⟩
    have hx : affine.x = point.x / point.z := by
      change ((factor : Word) * point.x) *
        ((factor : Word) * point.z)⁻¹ = point.x / point.z
      field_simp
    have hy : affine.y = point.y / point.z := by
      change ((factor : Word) * point.y) *
        ((factor : Word) * point.z)⁻¹ = point.y / point.z
      field_simp
    have hcurve : HomogeneousRCBG1GroupLaw.AffineOnCurve affine := by
      rw [show affine =
          ({ x := point.x / point.z, y := point.y / point.z } : Affine) by
        apply HomogeneousRCBG1GroupLaw.Affine.ext <;> assumption]
      exact normalized_onCurve point hvalid hz
    refine ⟨ofAffine affine hcurve, ?_, ?_⟩
    · unfold normalize
      rw [dif_neg hzRandomized]
      rw [dif_pos (show HomogeneousRCBG1GroupLaw.AffineOnCurve
        { x := randomized.x * randomized.z⁻¹,
          y := randomized.y * randomized.z⁻¹ } from hcurve)]
    · unfold toPoint FormulaSemantics.Law.decode
      have hzJacobian :
          HomogeneousRCBG1GroupLaw.toJacobian point (2 : Fin 3) ≠ 0 := by
        simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]
      rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero
        hvalid hzJacobian]
      simp [ofAffine, affine, HomogeneousRCBG1GroupLaw.toJacobian, hz,
        div_eq_mul_inv]
      constructor
      · exact hx.trans (by field_simp)
      · exact hy.trans (by field_simp)

theorem toPoint_eq_pointOfInput (point : Point) :
    toPoint point = FormulaSemantics.Law.pointOfInput point.1 point.2 := by
  rcases point with ⟨point, hpoint⟩
  cases point <;> rfl

/-- Native complete addition. -/
def add (left right : Point) : Except EvalError Point :=
  normalize (HomogeneousRCBG1GroupLaw.addFormula (encode left) (encode right))

theorem add_correct (left right : Point) :
    ∃ result : Point,
      add left right = .ok result ∧
        toPoint result = toPoint left + toPoint right := by
  let raw := HomogeneousRCBG1GroupLaw.addFormula (encode left) (encode right)
  have hvalid : BN254.curve.toJacobian.Nonsingular
      (HomogeneousRCBG1GroupLaw.toJacobian raw) :=
    by
      simpa [raw, encode] using
        HomogeneousRCBG1GroupLaw.toJacobian_formula_valid
          left.1 right.1 left.2 right.2
  obtain ⟨result, hnormalize, hresult⟩ := normalize_of_valid raw hvalid
  refine ⟨result, hnormalize, ?_⟩
  rw [hresult]
  have hdecode := FormulaSemantics.Law.decode_formula
    left.1 right.1 left.2 right.2
  rw [show raw = HomogeneousRCBG1GroupLaw.addFormula
      (HomogeneousRCBG1GroupLaw.encode left.1)
      (HomogeneousRCBG1GroupLaw.encode right.1) by rfl,
    hdecode, ← toPoint_eq_pointOfInput left,
    ← toPoint_eq_pointOfInput right]

def triple (point : Point) : Except EvalError Point := do
  let twice ← add point point
  add point twice

theorem triple_correct (point : Point) :
    ∃ result : Point,
      triple point = .ok result ∧ toPoint result = 3 • toPoint point := by
  obtain ⟨twice, htwice, htwicePoint⟩ := add_correct point point
  obtain ⟨result, hresult, hresultPoint⟩ := add_correct point twice
  refine ⟨result, ?_, ?_⟩
  · unfold triple
    rw [htwice]
    exact hresult
  · rw [hresultPoint, htwicePoint]
    simp [three_nsmul]

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

/-- Little-endian radix-three recomposition used by the native evaluator. -/
def recompose : List Point → Except EvalError Point
  | [] => .ok infinity
  | head :: tail => do
      let tailResult ← recompose tail
      let tripled ← triple tailResult
      add head tripled

theorem recompose_correct (points : List Point) :
    ∃ result : Point,
      recompose points = .ok result ∧
        toPoint result =
          TernaryFullWidth.recompose (points.map toPoint) := by
  induction points with
  | nil =>
      exact ⟨infinity, rfl, rfl⟩
  | cons head tail ih =>
      obtain ⟨tailResult, htail, htailPoint⟩ := ih
      obtain ⟨tripled, htripled, htripledPoint⟩ :=
        triple_correct tailResult
      obtain ⟨result, hresult, hresultPoint⟩ := add_correct head tripled
      refine ⟨result, ?_, ?_⟩
      · unfold recompose
        rw [htail]
        change (do
          let tripled ← triple tailResult
          add head tripled) = .ok result
        rw [htripled]
        exact hresult
      · rw [hresultPoint, htripledPoint, htailPoint]
        rfl

end GarblingPrize.Submission.RuntimeG1
