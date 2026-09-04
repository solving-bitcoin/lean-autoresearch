import GarblingPrize.Submission.FormulaSemantics

namespace GarblingPrize.Submission.G1CertificateBase

open GarblingPrize.Protected
open WeierstrassCurve

noncomputable section

abbrev Field := BN254.Fq
abbrev Affine := HomogeneousRCBG1GroupLaw.Affine
abbrev Raw := HomogeneousRCBG1GroupLaw.Homogeneous
abbrev Point := BN254.G1

/-- A finite affine checkpoint or infinity, carrying only the ordinary curve
equation.  Concrete coordinate equalities remain separate kernel-checked
certificate leaves. -/
structure Checkpoint where
  value : Option Affine
  onCurve : HomogeneousRCBG1GroupLaw.InputOnCurve value

def infinity : Checkpoint := ⟨none, trivial⟩

def affine (x y : Field)
    (h : HomogeneousRCBG1GroupLaw.AffineOnCurve ⟨x, y⟩) : Checkpoint :=
  ⟨some ⟨x, y⟩, h⟩

def semantic (checkpoint : Checkpoint) : Point :=
  FormulaSemantics.Law.pointOfInput checkpoint.value checkpoint.onCurve

def rawAdd (left right : Checkpoint) : Raw :=
  HomogeneousRCBG1GroupLaw.addFormula
    (HomogeneousRCBG1GroupLaw.encode left.value)
    (HomogeneousRCBG1GroupLaw.encode right.value)

/-- Equality of normalized ordinary-homogeneous coordinates is also complete
for the protected affine group.  This is the converse direction to the
privacy-facing alignment lemma in `FormulaSemantics`. -/
theorem decode_eq_semantic_of_normalize_eq
    (raw : Raw) (expected : Checkpoint)
    (hraw : BN254.curve.toJacobian.Nonsingular
      (HomogeneousRCBG1GroupLaw.toJacobian raw))
    (hnormalize : RepresentativeAlignment.normalize raw =
      RepresentativeAlignment.normalize
        (HomogeneousRCBG1GroupLaw.encode expected.value)) :
    FormulaSemantics.Law.decode raw = semantic expected := by
  rcases expected with ⟨expected, hexpected⟩
  cases expected with
  | none =>
      have hz : raw.z = 0 := by
        apply (RepresentativeAlignment.normalize_eq_none_iff raw).1
        rw [hnormalize]
        exact (RepresentativeAlignment.normalize_eq_none_iff _).2 rfl
      unfold FormulaSemantics.Law.decode semantic
      rw [show HomogeneousRCBG1GroupLaw.toJacobian raw =
          ![(1 : Field), 1, 0] by
        simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]]
      exact WeierstrassCurve.Jacobian.Point.toAffine_zero
  | some expected =>
      have hz : raw.z ≠ 0 := by
        intro hz
        have hleft := (RepresentativeAlignment.normalize_eq_none_iff raw).2 hz
        rw [hleft] at hnormalize
        simp [RepresentativeAlignment.normalize,
          HomogeneousRCBG1GroupLaw.encode,
          HomogeneousRCBG1GroupLaw.ofAffine] at hnormalize
      have hpair : (raw.x / raw.z, raw.y / raw.z) =
          (expected.x, expected.y) := by
        have h := hnormalize
        rw [RepresentativeAlignment.normalize_eq_some_of_z_ne_zero raw hz]
          at h
        simpa [RepresentativeAlignment.normalize,
          HomogeneousRCBG1GroupLaw.encode,
          HomogeneousRCBG1GroupLaw.ofAffine] using Option.some.inj h
      have hzj : HomogeneousRCBG1GroupLaw.toJacobian raw (2 : Fin 3) ≠ 0 := by
        simp [HomogeneousRCBG1GroupLaw.toJacobian, hz]
      unfold FormulaSemantics.Law.decode semantic
      rw [WeierstrassCurve.Jacobian.Point.toAffine_of_Z_ne_zero hraw hzj]
      change WeierstrassCurve.Affine.Point.some _ _ _ =
        WeierstrassCurve.Affine.Point.some expected.x expected.y _
      congr 1
      · have hx := congrArg Prod.fst hpair
        change raw.x / raw.z = expected.x at hx
        simp only [HomogeneousRCBG1GroupLaw.toJacobian, if_neg hz,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        change raw.x * raw.z / raw.z ^ 2 = expected.x
        calc
          raw.x * raw.z / raw.z ^ 2 = raw.x / raw.z := by field_simp
          _ = expected.x := hx
      · have hy := congrArg Prod.snd hpair
        change raw.y / raw.z = expected.y at hy
        simp only [HomogeneousRCBG1GroupLaw.toJacobian, if_neg hz,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
        change raw.y * raw.z ^ 2 / raw.z ^ 3 = expected.y
        calc
          raw.y * raw.z ^ 2 / raw.z ^ 3 = raw.y / raw.z := by field_simp
          _ = expected.y := hy

/-- Cross-multiplication form of a finite normalization certificate.  It
avoids inversions in every generated leaf. -/
theorem normalize_rawAdd_affine (left right : Checkpoint)
    (x y : Field)
    (hcurve : HomogeneousRCBG1GroupLaw.AffineOnCurve ⟨x, y⟩)
    (hz : (rawAdd left right).z ≠ 0)
    (hx : (rawAdd left right).x = x * (rawAdd left right).z)
    (hy : (rawAdd left right).y = y * (rawAdd left right).z) :
    RepresentativeAlignment.normalize (rawAdd left right) =
      RepresentativeAlignment.normalize
        (HomogeneousRCBG1GroupLaw.encode
          (affine x y hcurve).value) := by
  rw [RepresentativeAlignment.normalize_eq_some_of_z_ne_zero _ hz,
    RepresentativeAlignment.normalize_eq_some_of_z_ne_zero _ (by
      simp [affine, HomogeneousRCBG1GroupLaw.encode,
        HomogeneousRCBG1GroupLaw.ofAffine])]
  simp only [affine, HomogeneousRCBG1GroupLaw.encode,
    HomogeneousRCBG1GroupLaw.ofAffine, div_one]
  congr 2
  · exact (div_eq_iff hz).2 hx
  · exact (div_eq_iff hz).2 hy

/-- Normalization certificate for an addition whose result is infinity. -/
theorem normalize_rawAdd_infinity (left right : Checkpoint)
    (hz : (rawAdd left right).z = 0) :
    RepresentativeAlignment.normalize (rawAdd left right) =
      RepresentativeAlignment.normalize
        (HomogeneousRCBG1GroupLaw.encode infinity.value) := by
  exact (RepresentativeAlignment.normalize_eq_none_iff _).2 hz

/-- One checked RCB coordinate transition implies the corresponding complete
group-law transition. -/
theorem certifyAdd (left right result : Checkpoint)
    (hnormalize : RepresentativeAlignment.normalize (rawAdd left right) =
      RepresentativeAlignment.normalize
        (HomogeneousRCBG1GroupLaw.encode result.value)) :
    semantic result = semantic left + semantic right := by
  have hraw : BN254.curve.toJacobian.Nonsingular
      (HomogeneousRCBG1GroupLaw.toJacobian (rawAdd left right)) := by
    exact HomogeneousRCBG1GroupLaw.toJacobian_formula_valid _ _
      left.onCurve right.onCurve
  calc
    semantic result = FormulaSemantics.Law.decode (rawAdd left right) :=
      (decode_eq_semantic_of_normalize_eq
        (rawAdd left right) result hraw hnormalize).symm
    _ = semantic left + semantic right := by
      simpa only [rawAdd, semantic] using
        FormulaSemantics.Law.decode_formula left.value right.value
          left.onCurve right.onCurve

theorem certifyAddAffine (left right : Checkpoint) (x y : Field)
    (hcurve : HomogeneousRCBG1GroupLaw.AffineOnCurve ⟨x, y⟩)
    (hz : (rawAdd left right).z ≠ 0)
    (hx : (rawAdd left right).x = x * (rawAdd left right).z)
    (hy : (rawAdd left right).y = y * (rawAdd left right).z) :
    semantic (affine x y hcurve) = semantic left + semantic right :=
  certifyAdd left right (affine x y hcurve)
    (normalize_rawAdd_affine left right x y hcurve hz hx hy)

theorem certifyAddInfinity (left right : Checkpoint)
    (hz : (rawAdd left right).z = 0) :
    semantic infinity = semantic left + semantic right :=
  certifyAdd left right infinity (normalize_rawAdd_infinity left right hz)

def exponentStep (exponent : Nat) (bit : Bool) : Nat :=
  2 * exponent + if bit then 1 else 0

def pointStep (base accumulator : Point) (bit : Bool) : Point :=
  accumulator + accumulator + if bit then base else 0

theorem pointStep_nsmul (base : Point) (exponent : Nat) (bit : Bool) :
    pointStep base (exponent • base) bit = exponentStep exponent bit • base := by
  cases bit <;>
    simp [pointStep, exponentStep, add_nsmul] <;>
    rw [two_mul, add_nsmul]

theorem fold_pointStep_eq_nsmul (base : Point) (bits : List Bool)
    (exponent : Nat) :
    bits.foldl (pointStep base) (exponent • base) =
      bits.foldl exponentStep exponent • base := by
  induction bits generalizing exponent with
  | nil => rfl
  | cons bit tail ih =>
      simp only [List.foldl_cons]
      rw [pointStep_nsmul]
      exact ih (exponentStep exponent bit)

end

end GarblingPrize.Submission.G1CertificateBase
