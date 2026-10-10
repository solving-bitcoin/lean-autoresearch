import WotsLamport.Submission.CoefficientIndices
import WotsLamport.Submission.PolynomialLaw

namespace WotsLamport.Submission
open MeasureTheory ProbabilityTheory

/-- The implementation's linear address is a bijection onto all allocated
coefficient blocks, including the final unused true-label coefficients. -/
noncomputable def coefficientSlotEquiv : CoefficientSlot ≃ Fin coefficientCount :=
  Equiv.ofBijective coefficientIndex
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨coefficientIndex_injective, by simp [CoefficientSlot, coefficientCount]⟩)

noncomputable def coefficientFamilyEquiv (F : Type) :
    (Fin coefficientCount → F) ≃ (Fin 512 → Fin 16 → Fin 1023 → F) where
  toFun c := fun label limb degree => c (coefficientSlotEquiv (label, limb, degree))
  invFun c := fun index =>
    let slot := coefficientSlotEquiv.symm index
    c slot.1 slot.2.1 slot.2.2
  left_inv c := by
    funext index
    simp only [Prod.eta, Equiv.apply_symm_apply]
  right_inv c := by
    funext label limb degree
    simp only [Equiv.symm_apply_apply]

theorem uniform_coefficient_family {F : Type} [Finite F] [MeasurableSpace F]
    [DiscreteMeasurableSpace F] (event : Set (Fin 512 → Fin 16 → Fin 1023 → F)) :
    uniformOn (Set.univ : Set (Fin coefficientCount → F))
      {c | (fun label limb degree => c (coefficientIndex (label, limb, degree))) ∈ event} =
    uniformOn (Set.univ : Set (Fin 512 → Fin 16 → Fin 1023 → F)) event := by
  exact Shamir.uniform_event_equiv (coefficientFamilyEquiv F) event

end WotsLamport.Submission
