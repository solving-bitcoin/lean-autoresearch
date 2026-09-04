import GarblingPrize.Submission.HomogeneousRCBG1GroupLaw
import GarblingPrize.Submission.RepresentativeAlignment

namespace GarblingPrize.Submission.FormulaSemantics

open GarblingPrize.Protected
open WeierstrassCurve
open WeierstrassCurve.Jacobian

namespace Law

noncomputable section

abbrev Field := HomogeneousRCBG1GroupLaw.Field
abbrev Affine := HomogeneousRCBG1GroupLaw.Affine
abbrev Point := HomogeneousRCBG1GroupLaw.Homogeneous

theorem formula_wellFormed (left right : Option Affine)
    (hleft : HomogeneousRCBG1GroupLaw.InputOnCurve left)
    (hright : HomogeneousRCBG1GroupLaw.InputOnCurve right) :
    RepresentativeAlignment.WellFormed
      (HomogeneousRCBG1GroupLaw.addFormula
        (HomogeneousRCBG1GroupLaw.encode left)
        (HomogeneousRCBG1GroupLaw.encode right)) := by
  intro hz
  cases left with
  | none =>
      cases right with
      | none =>
          simp only [HomogeneousRCBG1GroupLaw.encode_none] at hz ⊢
          rw [HomogeneousRCBG1GroupLaw.formula_infinity_infinity]
          exact ⟨rfl, one_ne_zero⟩
      | some point =>
          simp only [HomogeneousRCBG1GroupLaw.encode_none,
            HomogeneousRCBG1GroupLaw.encode_some] at hz ⊢
          rw [HomogeneousRCBG1GroupLaw.formula_infinity_affine] at hz ⊢
          exact False.elim
            (HomogeneousRCBG1GroupLaw.affine_y_ne_zero point hright hz)
  | some leftPoint =>
      cases right with
      | none =>
          simp only [HomogeneousRCBG1GroupLaw.encode_none,
            HomogeneousRCBG1GroupLaw.encode_some] at hz ⊢
          rw [HomogeneousRCBG1GroupLaw.formula_affine_infinity] at hz ⊢
          exact False.elim
            (HomogeneousRCBG1GroupLaw.affine_y_ne_zero leftPoint hleft hz)
      | some rightPoint =>
          by_cases hx : leftPoint.x = rightPoint.x
          · have hySquare : leftPoint.y ^ 2 = rightPoint.y ^ 2 := by
              calc
                leftPoint.y ^ 2 = leftPoint.x ^ 3 +
                    HomogeneousRCBG1GroupLaw.curveB := hleft.symm
                _ = rightPoint.x ^ 3 +
                    HomogeneousRCBG1GroupLaw.curveB := by rw [hx]
                _ = rightPoint.y ^ 2 := hright
            rcases eq_or_eq_neg_of_sq_eq_sq leftPoint.y rightPoint.y hySquare with
              hy | hy
            · have hpoints : rightPoint = leftPoint := by
                cases leftPoint with
                | mk leftX leftY =>
                    cases rightPoint with
                    | mk rightX rightY =>
                        simp only at hx hy
                        subst rightX
                        subst rightY
                        rfl
              subst rightPoint
              exact False.elim
                (HomogeneousRCBG1GroupLaw.formula_self_z_ne_zero
                  leftPoint hleft hz)
            · have hpoints : rightPoint =
                  HomogeneousRCBG1GroupLaw.negAffine leftPoint := by
                cases leftPoint with
                | mk leftX leftY =>
                    cases rightPoint with
                    | mk rightX rightY =>
                        simp only at hx hy
                        subst rightX
                        simp only [HomogeneousRCBG1GroupLaw.negAffine]
                        congr
                        have hneg := congrArg (fun value : Field => -value) hy
                        simpa using hneg.symm
              subst rightPoint
              simp only [HomogeneousRCBG1GroupLaw.encode_some] at hz ⊢
              rw [HomogeneousRCBG1GroupLaw.formula_affine_neg leftPoint hleft]
                at hz ⊢
              exact ⟨rfl,
                HomogeneousRCBG1GroupLaw.formula_affine_neg_y_ne_zero
                  leftPoint hleft⟩
          · exact False.elim
              (HomogeneousRCBG1GroupLaw.formula_z_ne_zero_of_x_ne
                leftPoint rightPoint hleft hright hx hz)

def decode (point : Point) : BN254.G1 :=
  WeierstrassCurve.Jacobian.Point.toAffine BN254.curve.toJacobian
    (HomogeneousRCBG1GroupLaw.toJacobian point)

theorem toJacobian_x_of_z_ne (point : Point) (hz : point.z ≠ 0) :
    HomogeneousRCBG1GroupLaw.toJacobian point (0 : Fin 3) =
      point.x * point.z := by
  simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]

theorem toJacobian_y_of_z_ne (point : Point) (hz : point.z ≠ 0) :
    HomogeneousRCBG1GroupLaw.toJacobian point (1 : Fin 3) =
      point.y * point.z ^ 2 := by
  simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]

theorem toJacobian_z_of_z_ne (point : Point) (hz : point.z ≠ 0) :
    HomogeneousRCBG1GroupLaw.toJacobian point (2 : Fin 3) = point.z := by
  simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]

def pointOfInput : (input : Option Affine) →
    HomogeneousRCBG1GroupLaw.InputOnCurve input → BN254.G1
  | none, _ => 0
  | some point, h =>
      .some point.x point.y
        (HomogeneousRCBG1GroupLaw.affine_nonsingular point h)

theorem decode_encode (input : Option Affine)
    (hinput : HomogeneousRCBG1GroupLaw.InputOnCurve input) :
    decode (HomogeneousRCBG1GroupLaw.encode input) = pointOfInput input hinput := by
  cases input with
  | none =>
      simp [decode, HomogeneousRCBG1GroupLaw.toJacobian_infinity, pointOfInput,
        WeierstrassCurve.Jacobian.Point.toAffine_zero]
  | some point =>
      simp only [HomogeneousRCBG1GroupLaw.encode_some]
      unfold decode
      rw [HomogeneousRCBG1GroupLaw.toJacobian_ofAffine]
      rw [WeierstrassCurve.Jacobian.Point.toAffine_some
        (HomogeneousRCBG1GroupLaw.affineJacobian_valid point hinput)]
      rfl

theorem decode_formula (left right : Option Affine)
    (hleft : HomogeneousRCBG1GroupLaw.InputOnCurve left)
    (hright : HomogeneousRCBG1GroupLaw.InputOnCurve right) :
    decode
        (HomogeneousRCBG1GroupLaw.addFormula
          (HomogeneousRCBG1GroupLaw.encode left)
          (HomogeneousRCBG1GroupLaw.encode right)) =
      pointOfInput left hleft + pointOfInput right hright := by
  let result := HomogeneousRCBG1GroupLaw.addFormula
    (HomogeneousRCBG1GroupLaw.encode left)
    (HomogeneousRCBG1GroupLaw.encode right)
  let leftCoordinates := HomogeneousRCBG1GroupLaw.inputJacobian left
  let rightCoordinates := HomogeneousRCBG1GroupLaw.inputJacobian right
  have hresult := HomogeneousRCBG1GroupLaw.toJacobian_formula_valid
    left right hleft hright
  have hleftValid := HomogeneousRCBG1GroupLaw.inputJacobian_valid left hleft
  have hrightValid := HomogeneousRCBG1GroupLaw.inputJacobian_valid right hright
  have hclass := HomogeneousRCBG1GroupLaw.pointClass_formula
    left right hleft hright
  have hequiv : HomogeneousRCBG1GroupLaw.toJacobian result ≈
      BN254.curve.toJacobian.add leftCoordinates rightCoordinates := by
    exact Quotient.eq.mp hclass
  unfold decode
  rw [WeierstrassCurve.Jacobian.Point.toAffine_of_equiv hequiv]
  rw [WeierstrassCurve.Jacobian.Point.toAffine_add hleftValid hrightValid]
  rw [show WeierstrassCurve.Jacobian.Point.toAffine BN254.curve.toJacobian
        leftCoordinates = pointOfInput left hleft by
      dsimp only [leftCoordinates]
      rw [← HomogeneousRCBG1GroupLaw.toJacobian_encode]
      exact decode_encode left hleft]
  rw [show WeierstrassCurve.Jacobian.Point.toAffine BN254.curve.toJacobian
        rightCoordinates = pointOfInput right hright by
      dsimp only [rightCoordinates]
      rw [← HomogeneousRCBG1GroupLaw.toJacobian_encode]
      exact decode_encode right hright]

theorem normalize_eq_of_decode_eq {source target : Point}
    (hsource : BN254.curve.toJacobian.Nonsingular
      (HomogeneousRCBG1GroupLaw.toJacobian source))
    (htarget : BN254.curve.toJacobian.Nonsingular
      (HomogeneousRCBG1GroupLaw.toJacobian target))
    (hequal : decode source = decode target) :
    RepresentativeAlignment.normalize source =
      RepresentativeAlignment.normalize target := by
  by_cases hsourceZ : source.z = 0
  · have hsourceDecode : decode source = 0 := by
      unfold decode
      rw [show HomogeneousRCBG1GroupLaw.toJacobian source =
          ![(1 : Field), 1, 0] by
        simp [HomogeneousRCBG1GroupLaw.toJacobian, hsourceZ]]
      exact WeierstrassCurve.Jacobian.Point.toAffine_zero
    have htargetDecode : decode target = 0 := by rw [← hequal, hsourceDecode]
    have htargetZ : target.z = 0 := by
      by_contra hz
      have hzJ : HomogeneousRCBG1GroupLaw.toJacobian target (2 : Fin 3) ≠ 0 := by
        simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]
      unfold decode at htargetDecode
      rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero htarget hzJ]
        at htargetDecode
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ htargetDecode
    simp [RepresentativeAlignment.normalize, hsourceZ, htargetZ]
  · have hsourceDecode : decode source =
        .some _ _ ((BN254.curve.toJacobian.nonsingular_of_Z_ne_zero (by
          simp [HomogeneousRCBG1GroupLaw.toJacobian, hsourceZ])).mp
          hsource) := by
      have hsourceJZ :
          HomogeneousRCBG1GroupLaw.toJacobian source (2 : Fin 3) ≠ 0 := by
        simp [HomogeneousRCBG1GroupLaw.toJacobian, hsourceZ]
      unfold decode
      exact WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero
        hsource hsourceJZ
    have htargetZ : target.z ≠ 0 := by
      intro hz
      have htargetDecode : decode target = 0 := by
        unfold decode
        rw [show HomogeneousRCBG1GroupLaw.toJacobian target =
            ![(1 : Field), 1, 0] by
          simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]]
        exact WeierstrassCurve.Jacobian.Point.toAffine_zero
      rw [hsourceDecode, htargetDecode] at hequal
      exact WeierstrassCurve.Affine.Point.some_ne_zero _ hequal
    have htargetDecode : decode target =
        .some _ _ ((BN254.curve.toJacobian.nonsingular_of_Z_ne_zero (by
          simp [HomogeneousRCBG1GroupLaw.toJacobian, htargetZ])).mp
          htarget) := by
      have htargetJZ :
          HomogeneousRCBG1GroupLaw.toJacobian target (2 : Fin 3) ≠ 0 := by
        simp [HomogeneousRCBG1GroupLaw.toJacobian, htargetZ]
      unfold decode
      exact WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero
        htarget htargetJZ
    rw [RepresentativeAlignment.normalize_eq_some_of_z_ne_zero source hsourceZ,
      RepresentativeAlignment.normalize_eq_some_of_z_ne_zero target htargetZ]
    rw [hsourceDecode, htargetDecode] at hequal
    have hxy := WeierstrassCurve.Affine.Point.some.inj hequal
    have hx := hxy.left
    have hy := hxy.right
    simp only [toJacobian_x_of_z_ne source hsourceZ,
      toJacobian_y_of_z_ne source hsourceZ,
      toJacobian_z_of_z_ne source hsourceZ,
      toJacobian_x_of_z_ne target htargetZ,
      toJacobian_y_of_z_ne target htargetZ,
      toJacobian_z_of_z_ne target htargetZ] at hx hy
    congr 2
    · field_simp [hsourceZ, htargetZ] at hx ⊢
      simpa [mul_comm] using hx
    · field_simp [hsourceZ, htargetZ] at hy ⊢
      simpa [mul_comm] using hy

end

end Law

end GarblingPrize.Submission.FormulaSemantics
