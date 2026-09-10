import G1Release.Submission.G1Cardinality
import G1Release.Submission.FreeRandomness

namespace G1Release.Submission.Randomized
open G1Release.Math G1Release.Protected

def standardGenerator : BN254.G1 :=
  BN254.ofAffine ⟨1, by norm_num [baseFieldModulus]⟩
    ⟨2, by norm_num [baseFieldModulus]⟩ (by norm_num [BN254.OnCurve])

theorem standardGenerator_order :
    addOrderOf standardGenerator = scalarFieldModulus := by
  rw [show standardGenerator =
      G1GeneratorCertificateBase.generatorPoint by
    unfold standardGenerator G1GeneratorCertificateBase.generatorPoint
      G1GeneratorCertificateBase.generator G1CertificateBase.semantic
      G1CertificateBase.affine FormulaSemantics.Law.pointOfInput
    rfl]
  exact G1Cardinality.generator_addOrderOf

noncomputable def generatorEquiv : Fin scalarFieldModulus ≃ BN254.G1 :=
  Equiv.ofBijective
    (fun scalar : Fin scalarFieldModulus => scalar.val • standardGenerator)
    ((Nat.bijective_iff_injective_and_card _).2 ⟨by
      intro left right hequal
      apply Fin.ext
      exact nsmul_injOn_Iio_addOrderOf
        (by simpa [standardGenerator_order] using left.isLt)
        (by simpa [standardGenerator_order] using right.isLt)
        hequal,
      by
        rw [Nat.card_fin, G1Cardinality.pointCardinality]⟩)

@[simp] theorem generatorEquiv_apply (scalar : Fin scalarFieldModulus) :
    generatorEquiv scalar = scalar.val • standardGenerator := rfl

private theorem baseFieldUnits_positive : 0 < baseFieldModulus - 1 := by
  norm_num [baseFieldModulus]

private theorem unitValue_positive (value : (ZMod baseFieldModulus)ˣ) :
    0 < value.val.val := by
  have hne : value.val ≠ 0 := Units.ne_zero value
  have hval : value.val.val ≠ 0 := by
    intro hzero
    apply hne
    apply ZMod.val_injective
    simpa [hzero]
  omega

private theorem unitValue_pred_lt (value : (ZMod baseFieldModulus)ˣ) :
    value.val.val - 1 < baseFieldModulus - 1 := by
  have hlt := value.val.val_lt
  have hpos := unitValue_positive value
  omega

noncomputable def unitEquiv :
    Fin (baseFieldModulus - 1) ≃ (ZMod baseFieldModulus)ˣ where
  toFun value := Units.mk0 ((value.val + 1 : Nat) : ZMod baseFieldModulus) (by
    intro hzero
    have hdvd : baseFieldModulus ∣ value.val + 1 :=
      (ZMod.natCast_eq_zero_iff _ _).mp hzero
    have hle := Nat.le_of_dvd (by omega : 0 < value.val + 1) hdvd
    omega)
  invFun value := ⟨value.val.val - 1, unitValue_pred_lt value⟩
  left_inv value := by
    apply Fin.ext
    change (((value.val + 1 : Nat) : ZMod baseFieldModulus).val - 1) =
      value.val
    rw [ZMod.val_natCast_of_lt]
    · omega
    · omega
  right_inv value := by
    have hpos := unitValue_positive value
    apply Units.ext
    apply ZMod.val_injective
    change (((value.val.val - 1 + 1 : Nat) : ZMod baseFieldModulus).val) =
      value.val.val
    rw [ZMod.val_natCast_of_lt]
    · omega
    · have hlt := value.val.val_lt
      omega

@[simp] theorem unitEquiv_apply_val (value : Fin (baseFieldModulus - 1)) :
    ((unitEquiv value : (ZMod baseFieldModulus)ˣ) : ZMod baseFieldModulus) =
      (value.val + 1 : Nat) := rfl

noncomputable def wordEquiv : Fin baseFieldModulus ≃ BN254.Fq where
  toFun value := (value.val : ZMod baseFieldModulus)
  invFun value := ⟨value.val, value.val_lt⟩
  left_inv value := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt value.isLt
  right_inv value := by
    exact ZMod.natCast_zmod_val value

@[simp] theorem wordEquiv_val (value : Fin baseFieldModulus) :
    (wordEquiv value).val = value.val := by
  change ((value.val : ZMod baseFieldModulus)).val = value.val
  exact ZMod.val_natCast_of_lt value.isLt


end G1Release.Submission.Randomized
