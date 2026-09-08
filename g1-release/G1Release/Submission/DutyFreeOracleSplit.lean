import G1Release.Submission.DutyFreeRealIdeal
import G1Release.Submission.HintProductLaw
import G1Release.Submission.LamportLaw

/-! Regroup the infinite base oracle and finitely many auxiliary answers.
This allows a conditional finite bijection to be applied while retaining
all base-oracle answers seen by a bounded-query adversary. -/
namespace G1Release.Submission.DutyFreeOracleSplit
open SecretRelease MeasureTheory ProbabilityTheory DutyFreeSlots DutyFreeRealIdeal

abbrev Aux := Slot → Label

def aux (oracle : ExtendedOracle) : Aux := fun slot => oracle (.inr slot)

noncomputable def shuffle {X : Type*} [MeasurableSpace X] :
    (X × ExtendedOracle) ≃ᵐ (ROM.Oracle × X × Aux) where
  toFun s := (base s.2,s.1,aux s.2)
  invFun s := (s.2.1,Sum.elim s.1 s.2.2)
  left_inv s := by
    apply Prod.ext
    · rfl
    · funext q
      cases q <;> rfl
  right_inv s := rfl
  measurable_toFun := by
    apply (measurable_pi_lambda _ fun _ => (measurable_pi_apply _).comp measurable_snd).prodMk
    exact measurable_fst.prodMk (measurable_pi_lambda _ fun _ =>
      (measurable_pi_apply _).comp measurable_snd)
  measurable_invFun := by
    apply (measurable_fst.comp measurable_snd).prodMk
    apply measurable_pi_lambda
    intro q
    cases q with
    | inl query => exact (measurable_pi_apply query).comp measurable_fst
    | inr slot => exact (measurable_pi_apply slot).comp (measurable_snd.comp measurable_snd)

theorem aux_law : OracleLaw.law Slot = uniformOn (Set.univ : Set Aux) := by
  unfold OracleLaw.law
  rw [Measure.infinitePi_eq_pi, ← uniformOn_pi (f := fun _ : Slot => (Set.univ : Set Label))]
  simp

theorem shuffle_preserving {X : Type*} [MeasurableSpace X] [DiscreteMeasurableSpace X]
    [Finite X] [Nonempty X] :
    MeasurePreserving (shuffle (X := X))
      ((uniformOn (Set.univ : Set X)).prod (OracleLaw.law (List (Fin 256) ⊕ Slot)))
      ((OracleLaw.law (List (Fin 256))).prod (uniformOn (Set.univ : Set (X × Aux)))) := by
  let μx : Measure X := uniformOn Set.univ
  let μb : Measure ROM.Oracle := OracleLaw.law (List (Fin 256))
  let μa : Measure Aux := OracleLaw.law Slot
  have hs := (MeasurePreserving.id μx).prod
    (HintProductLaw.infinitePi_sum (X := fun _ : List (Fin 256) ⊕ Slot => Label)
      (fun _ => uniformOn (Set.univ : Set Label)))
  have h1 := (measurePreserving_prodAssoc μx μb μa).symm
    (MeasurableEquiv.prodAssoc : ((X × ROM.Oracle) × Aux) ≃ᵐ X × ROM.Oracle × Aux)
  have h2 := (Measure.measurePreserving_swap (μ := μx) (ν := μb)).prod
    (MeasurePreserving.id μa)
  have h3 := measurePreserving_prodAssoc μb μx μa
  have h := h3.comp (h2.comp (h1.comp hs))
  have hu : μx.prod μa = uniformOn (Set.univ : Set (X × Aux)) := by
    dsimp only [μx,μa]
    rw [aux_law, LamportLaw.prod_uniform_univ]
  rw [hu] at h
  exact h

end G1Release.Submission.DutyFreeOracleSplit
