import GarblingPrize.Submission.ProjectiveMap

namespace GarblingPrize.Submission.RepresentativeAlignment

open GarblingPrize.Protected

abbrev Word := BN254.Fq
abbrev Point := HomogeneousRCB.Point Word

def normalize (point : Point) : Option (Word × Word) :=
  if point.z = 0 then none else some (point.x / point.z, point.y / point.z)

def WellFormed (point : Point) : Prop :=
  point.z = 0 → point.x = 0 ∧ point.y ≠ 0

theorem normalize_eq_none_iff (point : Point) :
    normalize point = none ↔ point.z = 0 := by
  unfold normalize
  split <;> simp_all

theorem normalize_eq_some_of_z_ne_zero (point : Point) (hz : point.z ≠ 0) :
    normalize point = some (point.x / point.z, point.y / point.z) := by
  simp [normalize, hz]

theorem target_z_ne_zero {source target : Point}
    (hequal : normalize source = normalize target) (hz : source.z ≠ 0) :
    target.z ≠ 0 := by
  intro htarget
  have hsourceSome := normalize_eq_some_of_z_ne_zero source hz
  have htargetNone := (normalize_eq_none_iff target).2 htarget
  rw [hsourceSome, htargetNone] at hequal
  contradiction

theorem target_z_eq_zero {source target : Point}
    (hequal : normalize source = normalize target) (hz : source.z = 0) :
    target.z = 0 := by
  apply (normalize_eq_none_iff target).1
  rw [← hequal]
  exact (normalize_eq_none_iff source).2 hz

def factorValue (source target : Point) : Word :=
  if source.z = 0 then source.y / target.y else source.z / target.z

theorem factorValue_ne_zero {source target : Point}
    (hsource : WellFormed source) (htarget : WellFormed target)
    (hequal : normalize source = normalize target) :
    factorValue source target ≠ 0 := by
  unfold factorValue
  split
  · rename_i hz
    exact div_ne_zero (hsource hz).2
      (htarget (target_z_eq_zero hequal hz)).2
  · rename_i hz
    exact div_ne_zero hz (target_z_ne_zero hequal hz)

def factor (source target : Point)
    (hsource : WellFormed source) (htarget : WellFormed target)
    (hequal : normalize source = normalize target) : Wordˣ :=
  Units.mk0 (factorValue source target)
    (factorValue_ne_zero hsource htarget hequal)

theorem finite_coordinate_alignment {source target : Point}
    (hequal : normalize source = normalize target)
    (hsourceZ : source.z ≠ 0) :
    let scale := source.z / target.z
    scale * target.x = source.x ∧
      scale * target.y = source.y ∧
      scale * target.z = source.z := by
  have htargetZ := target_z_ne_zero hequal hsourceZ
  have hpair :
      (source.x / source.z, source.y / source.z) =
        (target.x / target.z, target.y / target.z) := by
    have := hequal
    rw [normalize_eq_some_of_z_ne_zero source hsourceZ,
      normalize_eq_some_of_z_ne_zero target htargetZ] at this
    exact Option.some.inj this
  dsimp only
  have hx := congrArg Prod.fst hpair
  have hy := congrArg Prod.snd hpair
  simp only [Prod.fst] at hx
  simp only [Prod.snd] at hy
  constructor
  · field_simp [hsourceZ, htargetZ] at hx ⊢
    exact hx.symm
  constructor
  · field_simp [hsourceZ, htargetZ] at hy ⊢
    exact hy.symm
  · exact div_mul_cancel₀ source.z htargetZ

theorem randomize_factor (source target : Point)
    (hsource : WellFormed source) (htarget : WellFormed target)
    (hequal : normalize source = normalize target) :
    HomogeneousRCB.randomize (factor source target hsource htarget hequal : Word)
        target = source := by
  unfold factor
  simp only [Units.val_mk0]
  by_cases hsourceZ : source.z = 0
  · have htargetZ := target_z_eq_zero hequal hsourceZ
    have hs := hsource hsourceZ
    have ht := htarget htargetZ
    apply HomogeneousRCB.Point.ext
    · simp only [factorValue, hsourceZ, if_pos, HomogeneousRCB.randomize]
      rw [ht.1, hs.1]
      simp
    · simp only [factorValue, hsourceZ, if_pos, HomogeneousRCB.randomize]
      exact div_mul_cancel₀ source.y ht.2
    · simp only [factorValue, hsourceZ, if_pos, HomogeneousRCB.randomize]
      rw [htargetZ]
      simp
  · have halign := finite_coordinate_alignment hequal hsourceZ
    have hfactor : factorValue source target = source.z / target.z := by
      simp [factorValue, hsourceZ]
    apply HomogeneousRCB.Point.ext
    · change factorValue source target * target.x = source.x
      rw [hfactor]
      exact halign.1
    · change factorValue source target * target.y = source.y
      rw [hfactor]
      exact halign.2.1
    · change factorValue source target * target.z = source.z
      rw [hfactor]
      exact halign.2.2

theorem factorValue_swapped (source target : Point)
    (hsource : WellFormed source) (htarget : WellFormed target)
    (hequal : normalize source = normalize target) :
    factorValue target source = (factorValue source target)⁻¹ := by
  unfold factorValue
  by_cases hsourceZ : source.z = 0
  · have htargetZ := target_z_eq_zero hequal hsourceZ
    simp only [hsourceZ, htargetZ, if_pos]
    exact (inv_div source.y target.y).symm
  · have htargetZ := target_z_ne_zero hequal hsourceZ
    simp only [hsourceZ, htargetZ, if_neg]
    exact (inv_div source.z target.z).symm

theorem factor_swapped (source target : Point)
    (hsource : WellFormed source) (htarget : WellFormed target)
    (hequal : normalize source = normalize target) :
    factor target source htarget hsource hequal.symm =
      (factor source target hsource htarget hequal)⁻¹ := by
  apply Units.ext
  change factorValue target source = (factorValue source target)⁻¹
  exact factorValue_swapped source target hsource htarget hequal

def randomizerEquiv (source target : Point)
    (hsource : WellFormed source) (htarget : WellFormed target)
    (hequal : normalize source = normalize target) : Wordˣ ≃ Wordˣ where
  toFun randomizer := randomizer * factor source target hsource htarget hequal
  invFun randomizer :=
    randomizer * (factor source target hsource htarget hequal)⁻¹
  left_inv randomizer := by simp [mul_assoc]
  right_inv randomizer := by simp [mul_assoc]

theorem randomize_randomizerEquiv (source target : Point)
    (hsource : WellFormed source) (htarget : WellFormed target)
    (hequal : normalize source = normalize target) (randomizer : Wordˣ) :
    HomogeneousRCB.randomize
        (randomizerEquiv source target hsource htarget hequal randomizer : Word)
        target =
      HomogeneousRCB.randomize (randomizer : Word) source := by
  change HomogeneousRCB.randomize
      ((randomizer : Word) *
        (factor source target hsource htarget hequal : Word)) target = _
  rw [show HomogeneousRCB.randomize
      ((randomizer : Word) *
        (factor source target hsource htarget hequal : Word)) target =
      HomogeneousRCB.randomize (randomizer : Word)
        (HomogeneousRCB.randomize
          (factor source target hsource htarget hequal : Word) target) by
    apply HomogeneousRCB.Point.ext <;>
      simp [HomogeneousRCB.randomize] <;> ring]
  rw [randomize_factor source target hsource htarget hequal]

theorem randomizerEquiv_symm_apply_eq_swapped (source target : Point)
    (hsource : WellFormed source) (htarget : WellFormed target)
    (hequal : normalize source = normalize target) (randomizer : Wordˣ) :
    (randomizerEquiv source target hsource htarget hequal).symm randomizer =
      randomizerEquiv target source htarget hsource hequal.symm randomizer := by
  change randomizer * (factor source target hsource htarget hequal)⁻¹ =
    randomizer * factor target source htarget hsource hequal.symm
  rw [factor_swapped source target hsource htarget hequal]

end GarblingPrize.Submission.RepresentativeAlignment
