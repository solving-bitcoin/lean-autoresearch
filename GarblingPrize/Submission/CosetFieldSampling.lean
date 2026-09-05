import GarblingPrize.Submission.CosetHintMap
import GarblingPrize.Submission.GLVCompactOracleLaw

namespace GarblingPrize.Submission.CosetFieldSampling

/-!
The nonzero elements of K=Fp(s) are parameterized by a projective direction
and a nonzero Fp radius. Direction infinity gives (0,r); finite direction t
gives (r,t*r). The inverse reads r from the first nonzero coordinate and t
as the coordinate ratio. This bijects (p+1)(p-1)=p²-1 samples with K*, so the
protected oracle can sample the multiplicative mask exactly without an
unbounded rejection loop in the submitted code.
-/

open GarblingPrize.Protected
open CosetCoordinates
open MeasureTheory ProbabilityTheory

/-- Used only to prove finite uniform laws; never enumerate p² elements at startup. -/
noncomputable instance : Fintype K :=
  Fintype.ofEquiv (Word × Word) (QuadraticAlgebra.equivProd 3 0).symm
instance : MeasurableSpace K := ⊤
instance : DiscreteMeasurableSpace K where
  forall_measurableSet := fun _ => MeasurableSpace.measurableSet_top

instance : MeasurableSpace Kˣ := ⊤
instance : DiscreteMeasurableSpace Kˣ where
  forall_measurableSet := fun _ => MeasurableSpace.measurableSet_top

def unitCoordinates : Option Word → Wordˣ → K
  | none, radius => ⟨0, radius⟩
  | some direction, radius => ⟨radius, direction * radius⟩

theorem unitCoordinates_ne_zero (direction : Option Word) (radius : Wordˣ) :
    unitCoordinates direction radius ≠ 0 := by
  cases direction with
  | none => exact fun h => Units.ne_zero radius (congrArg QuadraticAlgebra.im h)
  | some direction => exact fun h => Units.ne_zero radius (congrArg QuadraticAlgebra.re h)

def unitFromCoordinates (direction : Option Word) (radius : Wordˣ) : Kˣ :=
  Units.mk0 (unitCoordinates direction radius) (unitCoordinates_ne_zero direction radius)

theorem im_ne_zero_of_re_zero (value : Kˣ) (h : value.val.re = 0) : value.val.im ≠ 0 := by
  intro hi
  apply Units.ne_zero value
  ext <;> simp [h, hi]

def coordinatesFromUnit (value : Kˣ) : Option Word × Wordˣ :=
  if h : value.val.re = 0 then
    (none, Units.mk0 value.val.im (im_ne_zero_of_re_zero value h))
  else
    (some (value.val.im / value.val.re), Units.mk0 value.val.re h)

def unitCoordinatesEquiv : (Option Word × Wordˣ) ≃ Kˣ where
  toFun pair := unitFromCoordinates pair.1 pair.2
  invFun := coordinatesFromUnit
  left_inv := by
    rintro ⟨direction, radius⟩
    cases direction with
    | none =>
      simp only [coordinatesFromUnit, unitFromCoordinates, unitCoordinates, Units.val_mk0,
        ↓reduceDIte]
      apply Prod.ext
      · rfl
      · apply Units.ext; rfl
    | some direction =>
      simp only [coordinatesFromUnit, unitFromCoordinates, unitCoordinates, Units.val_mk0,
        Units.ne_zero, ↓reduceDIte, mul_div_cancel_right₀ _ (Units.ne_zero radius)]
      apply Prod.ext
      · rfl
      · apply Units.ext; rfl
  right_inv := by
    intro value
    unfold coordinatesFromUnit
    split
    · rename_i h
      apply Units.ext
      ext <;> simp [unitFromCoordinates, unitCoordinates, h]
    · rename_i h
      apply Units.ext
      ext <;> simp [unitFromCoordinates, unitCoordinates, h]

def directionEquiv : Fin (baseFieldModulus + 1) ≃ Option Word :=
  (finSuccEquiv baseFieldModulus).trans
    (Equiv.optionCongr (ZMod.finEquiv baseFieldModulus).toEquiv)

abbrev UnitSamples := Fin (baseFieldModulus + 1) × Fin (baseFieldModulus - 1)

instance : Nonempty UnitSamples :=
  ⟨(⟨0, by omega⟩, ⟨0, by norm_num [baseFieldModulus]⟩)⟩

noncomputable def unitSampleEquiv : UnitSamples ≃ Kˣ :=
  (Equiv.prodCongr directionEquiv GLVCompactOracleLaw.unitEquiv).trans unitCoordinatesEquiv

def radiusFromSample (sample : Fin (baseFieldModulus - 1)) : Wordˣ :=
  Units.mk0 ((sample.val + 1 : Nat) : Word) (by
    intro hzero
    have hdvd : baseFieldModulus ∣ sample.val + 1 :=
      (ZMod.natCast_eq_zero_iff _ _).mp hzero
    have hle := Nat.le_of_dvd (by omega : 0 < sample.val + 1) hdvd
    have hlt := sample.isLt
    omega)

def unitFromSamples (samples : UnitSamples) : Kˣ :=
  unitFromCoordinates (directionEquiv samples.1) (radiusFromSample samples.2)

@[simp] theorem unitFromSamples_eq (samples : UnitSamples) :
    unitFromSamples samples = unitSampleEquiv samples := by
  rfl

theorem unitSampleEquiv_preserves_uniform :
    MeasurePreserving unitSampleEquiv (uniformOn Set.univ) (uniformOn Set.univ) := by
  exact measurePreserving_uniformOfFiniteEquiv _

def fieldEquiv : (Word × Word) ≃ K := (QuadraticAlgebra.equivProd 3 0).symm

theorem fieldEquiv_preserves_uniform :
    MeasurePreserving fieldEquiv (uniformOn Set.univ) (uniformOn Set.univ) := by
  exact measurePreserving_uniformOfFiniteEquiv _

end GarblingPrize.Submission.CosetFieldSampling
