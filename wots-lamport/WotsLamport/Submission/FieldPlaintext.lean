import WotsLamport.Submission.ArtifactAnswerCoordinates
import WotsLamport.Submission.ActualPolynomialTable
import WotsLamport.Submission.VisibleCoefficientTransport

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

noncomputable def fieldPlaintextBytes (labels : Fin 256 → Pair) (c : AllocatedCoefficients)
    (position : SharePosition) : ByteArray :=
  concatenate ((List.finRange 16).map fun limb =>
    let slot : PolynomialSlot := (position.val.1,position.val.2.1,limb)
    writeLE 3 ((Shamir.coefficientPolynomial (labelLimb labels slot)
      (Shamir.coefficientPrefix (nonconstant_count_bound slot.2.1) (c slot))).eval
      ((position.val.2.2.val+1 : Nat) : ZMod 65537)).val)

theorem fieldPlaintextBytes_size (labels : Fin 256 → Pair) (c : AllocatedCoefficients)
    (position : SharePosition) : (fieldPlaintextBytes labels c position).size = 48 := by
  unfold fieldPlaintextBytes
  rw [concatenate_map_size (List.finRange 16) _ 3 (by intro limb _; exact writeLE_size 3 _)]
  rfl

noncomputable def fieldPlaintext (labels : Fin 256 → Pair) (c : AllocatedCoefficients)
    (position : SharePosition) : Bytes 48 :=
  ⟨(fieldPlaintextBytes labels c position).data, fieldPlaintextBytes_size labels c position⟩

/-- The exact 48-byte executable plaintext depends only on the allocated
field table and the fixed labels. This discharges the functional premise for
applying the joint modular-sampler comparison to the full artifact. -/
theorem idealPlaintext_as_fields (coins : Bytes randomnessBytes) (labels : Fin 256 → Pair)
    (position : SharePosition) :
    idealPlaintext (ByteArray.mk coins.toArray) labels position =
      fieldPlaintext labels (polynomialTableEquiv (actualFieldTable coins)) position := by
  apply Vector.toArray_inj.mp
  change (idealPlaintextBytes (ByteArray.mk coins.toArray) labels position).data =
    (fieldPlaintextBytes labels (polynomialTableEquiv (actualFieldTable coins)) position).data
  apply congrArg ByteArray.data
  unfold idealPlaintextBytes fieldPlaintextBytes
  apply congrArg concatenate
  apply List.ext_getElem (by simp)
  intro limb left right
  have hl : limb < 16 := by simpa using left
  simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
  rw [evaluatePolynomial_eq_val,
    actual_polynomial_table coins labels (position.val.1,position.val.2.1,⟨limb,hl⟩)]

def sharePositionVisible (m : Message) (position : SharePosition) : Prop :=
  encodeWord m (sharePositionEntry position).1 ≤ (sharePositionEntry position).2

theorem sharePosition_visible_coordinate (m : Message) (position : SharePosition)
    (visible : sharePositionVisible m position) :
    ((position.val.2.2.val+1 : Nat) : ZMod 65537) ∈
      visibleCoordinates m position.val.1 position.val.2.1 := by
  have indexed : (sharePositionEntry position,position.val.2.2.val) ∈
      (slots position.val.1 position.val.2.1).zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    have hb : position.val.2.2.val < (slots position.val.1 position.val.2.1).length := by
      rw [slots_length]
      exact position.property
    rw [getElem?_pos _ _ hb]
    rfl
  have member : (sharePositionEntry position,position.val.2.2.val) ∈
      visibleSlots m position.val.1 position.val.2.1 := by
    apply List.mem_filter.mpr
    exact ⟨indexed, by simpa only [decide_eq_true_eq] using visible⟩
  unfold visibleCoordinates
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨position.val.2.2.val+1,
    List.mem_map.mpr ⟨(sharePositionEntry position,position.val.2.2.val),member,rfl⟩,rfl⟩

/-- The concrete coefficient bijection preserves all 48 plaintext bytes at
every visible mask position, including all sixteen field limbs. -/
theorem fieldPlaintext_visible_transport (m : Message) (a b : Fin 256 → Pair)
    (selected : ∀ i, (a i).get (outputCodec.encode m)[i.val] =
      (b i).get (outputCodec.encode m)[i.val]) (c : AllocatedCoefficients)
    (position : SharePosition) (visible : sharePositionVisible m position) :
    fieldPlaintext b (visibleCoefficientEquiv m a b selected c) position =
      fieldPlaintext a c position := by
  apply Vector.toArray_inj.mp
  change (fieldPlaintextBytes b (visibleCoefficientEquiv m a b selected c) position).data =
    (fieldPlaintextBytes a c position).data
  apply congrArg ByteArray.data
  unfold fieldPlaintextBytes
  apply congrArg concatenate
  apply List.map_congr_left
  intro limb _
  rw [visibleCoefficientEquiv_eval m a b selected c
    (position.val.1,position.val.2.1,limb) _ (sharePosition_visible_coordinate m position visible)]

end WotsLamport.Submission
