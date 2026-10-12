import WotsLamport.Submission.VisiblePrivacy
import WotsLamport.Submission.PaddedPolynomialLaw

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

local instance VisibleCoefficientPrivacy.fieldMeasurable : MeasurableSpace (ZMod 65537) := ⊤

abbrev PolynomialSlot := Fin 256 × Bool × Fin 16

def labelLimb (labels : Fin 256 → Pair) (slot : PolynomialSlot) : ZMod 65537 :=
  readLE (ByteArray.mk ((labels slot.1).get slot.2.1).toArray) (2*slot.2.2.val) 2

theorem nonconstant_count_bound (value : Bool) : threshold value-1 ≤ 1023 := by
  cases value <;> decide

noncomputable def visibleCoefficientObservations (m : Message) (labels : Fin 256 → Pair)
    (c : PolynomialSlot → Fin 1023 → ZMod 65537) :
    (slot : PolynomialSlot) → visibleCoordinates m slot.1 slot.2.1 → ZMod 65537 :=
  fun slot => Shamir.observedValues (visibleCoordinates m slot.1 slot.2.1)
    (Shamir.coefficientEquiv (labelLimb labels slot) (threshold slot.2.1-1)
      (Shamir.coefficientPrefix (nonconstant_count_bound slot.2.1) (c slot)))

/-- Under uniform allocated field coefficients, the entire visible-share
family is unchanged in law when opposite labels change. Selected labels and
their full visible evaluations are retained in the same joint event. This is
a sharing-layer theorem; encrypted bytes and oracle transcripts are separate. -/
theorem visible_coefficients_joint_privacy (m : Message) (a b : Fin 256 → Pair)
    (selected : ∀ i, (a i).get (outputCodec.encode m)[i.val] =
      (b i).get (outputCodec.encode m)[i.val])
    (event : Set ((slot : PolynomialSlot) → visibleCoordinates m slot.1 slot.2.1 → ZMod 65537)) :
    uniformOn (Set.univ : Set (PolynomialSlot → Fin 1023 → ZMod 65537))
      {c | visibleCoefficientObservations m a c ∈ event} =
    uniformOn (Set.univ : Set (PolynomialSlot → Fin 1023 → ZMod 65537))
      {c | visibleCoefficientObservations m b c ∈ event} := by
  unfold visibleCoefficientObservations
  apply Shamir.uniform_padded_joint_secret_transport (F := ZMod 65537) (I := PolynomialSlot) 1023
    (fun slot => threshold slot.2.1-1) (fun slot => nonconstant_count_bound slot.2.1)
    (fun slot => visibleCoordinates m slot.1 slot.2.1)
    (fun slot => visibleCoordinates_nonzero m slot.1 slot.2.1)
    (labelLimb a) (labelLimb b) _ event
  intro slot
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

end WotsLamport.Submission
