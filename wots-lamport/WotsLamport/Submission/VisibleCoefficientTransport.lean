import WotsLamport.Submission.VisibleCoefficientPrivacy

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

abbrev AllocatedCoefficients := PolynomialSlot → Fin 1023 → ZMod 65537

theorem visible_limb_transport_valid (m : Message) (a b : Fin 256 → Pair)
    (selected : ∀ i, (a i).get (outputCodec.encode m)[i.val] =
      (b i).get (outputCodec.encode m)[i.val]) (slot : PolynomialSlot) :
    labelLimb a slot = labelLimb b slot ∨
      (visibleCoordinates m slot.1 slot.2.1).card < threshold slot.2.1-1+1 := by
  by_cases hv : slot.2.1 = (outputCodec.encode m)[slot.1.val]
  · left
    unfold labelLimb
    rw [hv, selected slot.1]
  · right
    have hop : slot.2.1 = !(outputCodec.encode m)[slot.1.val] := by
      cases h : (outputCodec.encode m)[slot.1.val] <;>
        cases h' : slot.2.1 <;> simp_all
    have ht : threshold slot.2.1-1+1 = threshold slot.2.1 := by
      cases slot.2.1 <;> decide
    rw [ht, hop]
    exact opposite_visibleCoordinates_few m slot.1

/-- A concrete bijection on every allocated coefficient. Selected-label
polynomials stay fixed; opposite-label polynomials shift by a vanishing
polynomial on the visible evaluation coordinates. Unused coefficients remain
part of the same sample space. -/
noncomputable def visibleCoefficientEquiv (m : Message) (a b : Fin 256 → Pair)
    (selected : ∀ i, (a i).get (outputCodec.encode m)[i.val] =
      (b i).get (outputCodec.encode m)[i.val]) :
    AllocatedCoefficients ≃ AllocatedCoefficients := by
  classical
  exact Equiv.piCongrRight fun slot =>
    if he : labelLimb a slot = labelLimb b slot then Equiv.refl _ else
      Shamir.paddedCoefficientEquiv (nonconstant_count_bound slot.2.1)
        (Shamir.coefficientSecretEquiv (visibleCoordinates m slot.1 slot.2.1)
          (visibleCoordinates_nonzero m slot.1 slot.2.1) (threshold slot.2.1-1)
          ((visible_limb_transport_valid m a b selected slot).resolve_left he)
          (labelLimb a slot) (labelLimb b slot))

theorem visibleCoefficientEquiv_observed (m : Message) (a b : Fin 256 → Pair)
    (selected : ∀ i, (a i).get (outputCodec.encode m)[i.val] =
      (b i).get (outputCodec.encode m)[i.val]) (c : AllocatedCoefficients) :
    visibleCoefficientObservations m b (visibleCoefficientEquiv m a b selected c) =
      visibleCoefficientObservations m a c := by
  classical
  funext slot
  by_cases he : labelLimb a slot = labelLimb b slot
  · simp only [visibleCoefficientObservations, visibleCoefficientEquiv,
      Equiv.piCongrRight_apply, Pi.map_apply, dif_pos he, Equiv.refl_apply]
    rw [he]
  · change Shamir.observedValues (visibleCoordinates m slot.1 slot.2.1)
      (Shamir.coefficientEquiv (labelLimb b slot) (threshold slot.2.1-1)
        (Shamir.coefficientPrefix (nonconstant_count_bound slot.2.1)
          (visibleCoefficientEquiv m a b selected c slot))) = _
    simp only [visibleCoefficientEquiv, Equiv.piCongrRight_apply, Pi.map_apply, dif_neg he]
    change Shamir.observedValues (visibleCoordinates m slot.1 slot.2.1)
      (Shamir.coefficientEquiv (labelLimb b slot) (threshold slot.2.1-1)
        (Shamir.coefficientPrefix (nonconstant_count_bound slot.2.1)
          (Shamir.replaceCoefficientPrefix (nonconstant_count_bound slot.2.1) _ (c slot)))) = _
    rw [Shamir.coefficientPrefix_replace]
    exact Shamir.coefficientSecretEquiv_observed _ _ _ _ _ _ _

/-- Pointwise equality at any actually visible share coordinate. This is the
bridge needed before applying a byte-level ciphertext transport. -/
theorem visibleCoefficientEquiv_eval (m : Message) (a b : Fin 256 → Pair)
    (selected : ∀ i, (a i).get (outputCodec.encode m)[i.val] =
      (b i).get (outputCodec.encode m)[i.val]) (c : AllocatedCoefficients)
    (slot : PolynomialSlot) (point : ZMod 65537)
    (member : point ∈ visibleCoordinates m slot.1 slot.2.1) :
    (Shamir.coefficientPolynomial (labelLimb b slot)
      (Shamir.coefficientPrefix (nonconstant_count_bound slot.2.1)
        (visibleCoefficientEquiv m a b selected c slot))).eval point =
    (Shamir.coefficientPolynomial (labelLimb a slot)
      (Shamir.coefficientPrefix (nonconstant_count_bound slot.2.1) (c slot))).eval point := by
  exact congrFun (congrFun (visibleCoefficientEquiv_observed m a b selected c) slot) ⟨point,member⟩

end WotsLamport.Submission
