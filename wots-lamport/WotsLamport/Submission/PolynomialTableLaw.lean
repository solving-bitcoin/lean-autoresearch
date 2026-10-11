import WotsLamport.Submission.CoefficientTableLaw
import WotsLamport.Submission.VisibleCoefficientPrivacy

namespace WotsLamport.Submission
open MeasureTheory ProbabilityTheory

local instance : MeasurableSpace (ZMod 65537) := ⊤

/-- A polynomial family slot and a degree determine their actual byte-block
address. Every allocated address appears exactly once. -/
def polynomialAddress (entry : PolynomialSlot × Fin 1023) : Fin coefficientCount :=
  coefficientIndex (labelIndex entry.1.1 entry.1.2.1, entry.1.2.2, entry.2)

theorem polynomialAddress_injective : Function.Injective polynomialAddress := by
  intro a b he
  have hs := coefficientIndex_injective he
  have hl : (a.1.1, a.1.2.1) = (b.1.1, b.1.2.1) :=
    labelIndex_injective (congrArg Prod.fst hs)
  have hlimb := congrArg (fun s : CoefficientSlot => s.2.1) hs
  have hdegree := congrArg (fun s : CoefficientSlot => s.2.2) hs
  exact Prod.ext
    (Prod.ext (congrArg (fun pair : Fin 256 × Bool => pair.1) hl)
      (Prod.ext (congrArg (fun pair : Fin 256 × Bool => pair.2) hl) hlimb)) hdegree

noncomputable def polynomialAddressEquiv : (PolynomialSlot × Fin 1023) ≃ Fin coefficientCount :=
  Equiv.ofBijective polynomialAddress
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨polynomialAddress_injective, by simp only [PolynomialSlot, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]; rfl⟩)

noncomputable def polynomialTableEquiv :
    (Fin coefficientCount → ZMod 65537) ≃ (PolynomialSlot → Fin 1023 → ZMod 65537) where
  toFun c := fun slot degree => c (polynomialAddressEquiv (slot, degree))
  invFun c := fun index =>
    let entry := polynomialAddressEquiv.symm index
    c entry.1 entry.2
  left_inv c := by
    funext index
    simp only [Prod.eta, Equiv.apply_symm_apply]
  right_inv c := by
    funext slot degree
    simp only [Equiv.symm_apply_apply]

/-- The sharing-layer privacy theorem uses precisely the implementation's
flat allocated field table, reindexed by its proved address bijection. -/
theorem uniform_flat_visible_privacy (m : WotsLamport.Protected.Message)
    (a b : Fin 256 → SecretRelease.Pair)
    (selected : ∀ i, (a i).get (WotsLamport.Protected.outputCodec.encode m)[i.val] =
      (b i).get (WotsLamport.Protected.outputCodec.encode m)[i.val])
    (event : Set ((slot : PolynomialSlot) → visibleCoordinates m slot.1 slot.2.1 → ZMod 65537)) :
    uniformOn (Set.univ : Set (Fin coefficientCount → ZMod 65537))
      {c | visibleCoefficientObservations m a (polynomialTableEquiv c) ∈ event} =
    uniformOn (Set.univ : Set (Fin coefficientCount → ZMod 65537))
      {c | visibleCoefficientObservations m b (polynomialTableEquiv c) ∈ event} := by
  calc
    _ = uniformOn (Set.univ : Set (PolynomialSlot → Fin 1023 → ZMod 65537))
        {c | visibleCoefficientObservations m a c ∈ event} :=
      Shamir.uniform_event_equiv polynomialTableEquiv _
    _ = uniformOn (Set.univ : Set (PolynomialSlot → Fin 1023 → ZMod 65537))
        {c | visibleCoefficientObservations m b c ∈ event} :=
      visible_coefficients_joint_privacy m a b selected event
    _ = _ := (Shamir.uniform_event_equiv polynomialTableEquiv _).symm

end WotsLamport.Submission
