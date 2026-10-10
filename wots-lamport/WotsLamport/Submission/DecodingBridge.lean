import WotsLamport.Submission.ByteBridge
import WotsLamport.Submission.ArtifactBridge
import WotsLamport.Submission.Exposed
import WotsLamport.Submission.InterpolationBridge

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- Once the body slice is identified with its stored ciphertext, honest
forward-chain evaluation and exact field decoding recover this share row.
The slice premise is a serialization obligation, not a security assumption. -/
theorem decodeShare_of_slice (h : Hash) (coins pk nonce body : ByteArray)
    (keys : Keys) (m : Message) (i : Fin 256) (value : Bool) (label : Label)
    (entry : (Fin 67 × Nat) × Nat) (he : entry ∈ visibleSlots m i value)
    (slice : body.extract
        (32 + 512*32 + (i.val*(1984+1982) + if value then 1984 else 0)*48 + entry.2*48)
        (32 + 512*32 + (i.val*(1984+1982) + if value then 1984 else 0)*48 + (entry.2+1)*48) =
      (labelTable h coins pk nonce keys i value label).extract (entry.2*48) ((entry.2+1)*48)) :
    decodeShare h pk nonce body m (sign h keys m) i value entry =
      some (entry.2+1, (List.range 16).map fun limb =>
        evaluatePolynomial (polynomial coins label i.val limb value) (entry.2+1)) := by
  obtain ⟨hidx, hslot⟩ := visibleSlots_lookup m i value entry he
  have hopen := visibleSlots_open m i value entry he
  have hplain := labelTable_decrypt h coins pk nonce keys i value label entry.2 hidx
  rw [hslot] at hplain
  have hfields : (List.range 16).map (fun limb =>
      readLE (concatenate ((List.range 16).map fun j => writeLE 3
        (evaluatePolynomial (polynomial coins label i.val j value) (entry.2+1)))) (3*limb) 3) =
      (List.range 16).map (fun limb =>
        evaluatePolynomial (polynomial coins label i.val limb value) (entry.2+1)) := by
    apply List.map_congr_left
    intro limb hl
    exact read_share_limb _ _ limb (List.mem_range.mp hl)
  have hvalid : ((List.range 16).map fun limb =>
      evaluatePolynomial (polynomial coins label i.val limb value) (entry.2+1)).any
      (fun x => decide (x ≥ prime)) = false := by
    apply List.any_eq_false.mpr
    intro n hn
    obtain ⟨limb, _, rfl⟩ := List.mem_map.mp hn
    simpa using Nat.not_le.mpr (evaluatePolynomial_lt
      (polynomial coins label i.val limb value) (entry.2+1))
  rcases entry with ⟨⟨j, k⟩, index⟩
  dsimp only at *
  unfold decodeShare
  dsimp only
  rw [forward_closure h keys m j k hopen, slice, hplain, hfields, hvalid]
  rfl

theorem decodeShare_prepared (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) (hcoins : 32 ≤ coins.size)
    (m : Message) (i : Fin 256) (value : Bool)
    (entry : (Fin 67 × Nat) × Nat) (he : entry ∈ visibleSlots m i value) :
    decodeShare h (keyCodec.encode (publicKey h keys)) (coins.extract 0 32)
      (prepare h coins keys labels) m (sign h keys m) i value entry =
      some (entry.2+1, (List.range 16).map fun limb =>
        evaluatePolynomial (polynomial coins ((labels i).get value) i.val limb value) (entry.2+1)) := by
  apply decodeShare_of_slice h coins _ _ _ keys m i value ((labels i).get value) entry he
  obtain ⟨hidx, _⟩ := visibleSlots_lookup m i value entry he
  exact prepare_share_slice h coins keys labels hcoins i value entry.2 hidx

theorem mapM_eq_some_map {A B : Type} (xs : List A) (f : A → Option B) (g : A → B)
    (hf : ∀ x ∈ xs, f x = some (g x)) : xs.mapM f = some (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp [List.mapM_cons, hx, ht]

def honestRows (coins : ByteArray) (label : Label) (m : Message) (i : Fin 256)
    (value : Bool) : List (Nat × List Nat) :=
  (visibleSlots m i value).map fun entry => (entry.2+1, (List.range 16).map fun limb =>
    evaluatePolynomial (polynomial coins label i.val limb value) (entry.2+1))

theorem decodeShares_prepared (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) (hcoins : 32 ≤ coins.size)
    (m : Message) (i : Fin 256) (value : Bool) :
    (visibleSlots m i value).mapM
      (decodeShare h (keyCodec.encode (publicKey h keys)) (coins.extract 0 32)
        (prepare h coins keys labels) m (sign h keys m) i value) =
      some (honestRows coins ((labels i).get value) m i value) := by
  exact mapM_eq_some_map _ _ _ (decodeShare_prepared h coins keys labels hcoins m i value)

/-- The actual selected rows meet the degree and coordinate premises of
the executable interpolation theorem. This result still precedes repacking
and the label commitment check in expandLabel. -/
theorem interpolate_honestRows (coins : ByteArray) (label : Label) (m : Message) (i : Fin 256) :
    interpolate (honestRows coins label m i (outputCodec.encode m)[i.val]) =
      (List.range 16).map (fun limb =>
        evaluatePolynomial (polynomial coins label i.val limb (outputCodec.encode m)[i.val]) 0) := by
  apply interpolate_reconstruct_nat
  · simpa only [honestRows, List.map_map, Function.comp_def] using
      visibleSlots_distinct m i (outputCodec.encode m)[i.val]
  · intro row hr
    obtain ⟨entry, he, rfl⟩ := List.mem_map.mp hr
    exact (visibleSlots_bounds m i _ entry he).2
  · intro limb _
    simpa only [honestRows, List.length_map, visibleSlots_selected_length] using
      polynomial_degree coins label i.val limb (outputCodec.encode m)[i.val]
  · intro row hr limb hl
    obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hr
    rw [getElem!_pos _ limb (by simpa using hl)]
    simp only [List.getElem_map, List.getElem_range]
    exact (evaluatePolynomial_field _ _).symm

end WotsLamport.Submission
