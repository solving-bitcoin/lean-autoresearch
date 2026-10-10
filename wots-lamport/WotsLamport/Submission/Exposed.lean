import WotsLamport.Submission.Layout

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

private theorem uniform_suffix (D c w : Nat) :
    ((List.range D).map fun k => if c ≤ k then w else 0).sum = (D-c)*w := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_singleton, List.sum_singleton]
    by_cases h : c ≤ D
    · have hs : D+1-c = D-c+1 := by omega
      simp [h, hs, Nat.add_mul]
    · have h0 : D-c = 0 := by omega
      have h1 : D+1-c = 0 := by omega
      simp [h, h0, h1]

set_option maxRecDepth 4096 in
private theorem nibble_suffix (r : Fin 4) (value : Bool) (c : Fin 16) :
    ((List.range 15).map fun k => if c.val ≤ k then
      (multiplicity 1 (fun d => d.testBit r.val == value) k).toNat else 0).sum +
      (if value then 1 else 0) =
      15-c.val + (if c.val.testBit r.val == value then 1 else 0) := by
  revert r value c
  decide +kernel

/-- Count the actually enumerated slots whose mask key lies in the forward
closure. Each replicate is a different interpolation coordinate. -/
def exposedCount (m : Message) (i : Fin 256) (value : Bool) (j : Fin 67) : Nat :=
  ((List.range (maximum j)).map fun k => if encodeWord m j ≤ k then
    if j = targetChain i then (multiplicity (weight j) (holds i value) k).toNat
    else weight j else 0).sum

theorem filtered_slots_length (m : Message) (i : Fin 256) (value : Bool) :
    ((slots i value).filter fun jk => decide (encodeWord m jk.1 ≤ jk.2)).length =
      ∑ j : Fin 67, exposedCount m i value j := by
  simp only [slots, List.filter_flatMap, List.length_flatMap, List.filter_replicate]
  rw [← Fin.sum_univ_def]
  apply Finset.sum_congr rfl
  intro j _
  unfold exposedCount
  apply congrArg List.sum
  apply List.map_congr_left
  intro k _
  by_cases h : encodeWord m j ≤ k <;> simp [h]

theorem exposed_chain_count (m : Message) (i : Fin 256) (value : Bool) (j : Fin 67) :
    exposedCount m i value j + (if j = targetChain i then (if value then 1 else 0) else 0) =
      weight j * (maximum j - encodeWord m j) +
        (if j = targetChain i then (if holds i value (encodeWord m j) then 1 else 0) else 0) := by
  by_cases h : j = targetChain i
  · subst j
    have hd : encodeWord m (targetChain i) < 16 := by
      have he := encodeWord_le m (targetChain i)
      rw [target_maximum] at he
      omega
    simpa [exposedCount, target_maximum, target_weight,
      Nat.one_mul, holds, digitBit] using
      nibble_suffix ⟨bitInNibble i, Nat.mod_lt i.val (by decide)⟩ value
        ⟨encodeWord m (targetChain i), hd⟩
  · simp [exposedCount, h, uniform_suffix, Nat.mul_comm]

theorem exposed_total_count (m : Message) (i : Fin 256) (value : Bool) :
    (∑ j : Fin 67, exposedCount m i value j) + (if value then 1 else 0) =
      1023 + (if holds i value (encodeWord m (targetChain i)) then 1 else 0) := by
  have he : (∑ j : Fin 67, (exposedCount m i value j +
      (if j = targetChain i then (if value then 1 else 0) else 0))) =
      ∑ j : Fin 67, (weight j * (maximum j - encodeWord m j) +
        (if j = targetChain i then (if holds i value (encodeWord m j) then 1 else 0) else 0)) := by
    apply Finset.sum_congr rfl
    intro j _
    exact exposed_chain_count m i value j
  simpa [Finset.sum_add_distrib, remaining_weighted_sum] using he

theorem selected_exposed_count (m : Message) (i : Fin 256) :
    (∑ j : Fin 67, exposedCount m i (outputCodec.encode m)[i.val] j) =
      threshold (outputCodec.encode m)[i.val] := by
  have he := exposed_total_count m i (outputCodec.encode m)[i.val]
  rw [selected_holds] at he
  cases hv : (outputCodec.encode m)[i.val] <;> simp [hv, threshold] at he ⊢ <;> omega

theorem opposite_exposed_count (m : Message) (i : Fin 256) :
    (∑ j : Fin 67, exposedCount m i (!(outputCodec.encode m)[i.val]) j) + 1 =
      threshold (!(outputCodec.encode m)[i.val]) := by
  have he := exposed_total_count m i (!(outputCodec.encode m)[i.val])
  rw [opposite_does_not_hold] at he
  cases hv : (outputCodec.encode m)[i.val] <;> simp [hv, threshold] at he ⊢ <;> omega

theorem selected_slots_length (m : Message) (i : Fin 256) :
    ((slots i (outputCodec.encode m)[i.val]).filter
      fun jk => decide (encodeWord m jk.1 ≤ jk.2)).length =
      threshold (outputCodec.encode m)[i.val] := by
  rw [filtered_slots_length, selected_exposed_count]

theorem opposite_slots_length (m : Message) (i : Fin 256) :
    ((slots i (!(outputCodec.encode m)[i.val])).filter
      fun jk => decide (encodeWord m jk.1 ≤ jk.2)).length + 1 =
      threshold (!(outputCodec.encode m)[i.val]) := by
  rw [filtered_slots_length, opposite_exposed_count]

end WotsLamport.Submission
