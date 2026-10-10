import WotsLamport.Submission.DecodingBridge
import WotsLamport.Submission.LabelBridge

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- Every selected label is recovered from the same prepared artifact,
for every message, oracle, key, label table and sufficiently long coin string. -/
theorem expandLabel_prepared (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) (hcoins : 32 ≤ coins.size) (m : Message) (i : Fin 256) :
    expandLabel h (keyCodec.encode (publicKey h keys)) (coins.extract 0 32)
      (prepare h coins keys labels) m (sign h keys m) i (outputCodec.encode m)[i.val] =
      some (ByteArray.mk ((labels i).get (outputCodec.encode m)[i.val]).toArray) := by
  let value := (outputCodec.encode m)[i.val]
  let label := (labels i).get value
  let limbs := (List.range 16).map fun limb => readLE (ByteArray.mk label.toArray) (2*limb) 2
  have hlength : (honestRows coins label m i value).length = threshold value := by
    change ((visibleSlots m i value).map _).length = threshold value
    rw [List.length_map]
    exact visibleSlots_selected_length m i
  have hrec : interpolate (honestRows coins label m i value) = limbs := by
    apply (interpolate_honestRows coins label m i).trans
    apply List.map_congr_left
    intro limb _
    exact polynomial_eval_zero coins label i.val limb value
  have hvalid : limbs.any (fun x => decide (x ≥ 65536)) = false := by
    apply List.any_eq_false.mpr
    intro n hn
    obtain ⟨limb, _, rfl⟩ := List.mem_map.mp hn
    simpa using Nat.not_le.mpr (readLE_two_lt (ByteArray.mk label.toArray) (2*limb))
  have hbytes : concatenate (limbs.map (writeLE 2)) = ByteArray.mk label.toArray := by
    simpa only [limbs, List.map_map, Function.comp_def] using serialize_label_limbs label
  change expandLabel h _ _ _ m _ i value = some (ByteArray.mk label.toArray)
  simp only [expandLabel, decodeShares_prepared h coins keys labels hcoins m i value]
  dsimp only [label] at hlength hrec hbytes
  simp only [hlength, hrec, hvalid, hbytes, byteVector_decode_raw, Option.bind_some,
    bne_self_eq_false, Bool.false_eq_true, ite_false,
    prepare_commitment_slice h coins keys labels hcoins i value] <;> rfl

theorem concatenate_label_fold (labels : List Label) (initial : ByteArray) :
    (labels.map fun label => ByteArray.mk label.toArray).foldl
      (fun acc bytes => acc ++ bytes) initial =
      ByteArray.mk (labels.foldl (fun acc label => acc ++ label.toArray) initial.data) := by
  induction labels generalizing initial with
  | nil => rfl
  | cons label rest ih =>
    simpa only [List.map_cons, List.foldl_cons, ByteArray.data_append] using ih (initial ++ ByteArray.mk label.toArray)

theorem concatenate_labels (labels : List Label) :
    concatenate (labels.map fun label => ByteArray.mk label.toArray) = pack labels := by
  exact concatenate_label_fold labels ByteArray.empty

set_option maxRecDepth 4096 in
theorem expand_prepared (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) (hcoins : 32 ≤ coins.size) (m : Message) :
    expand h (publicKey h keys) (prepare h coins keys labels) m (sign h keys m) =
      some (pack ((List.finRange 256).map fun i => (labels i).get (outputCodec.encode m)[i.val])) := by
  have hn : (coins.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  have hs : (prepare h coins keys labels).size = bodyBytes := by
    rw [prepare_size, hn]
    rfl
  have hm := mapM_eq_some_map (List.finRange 256)
    (fun i => expandLabel h (keyCodec.encode (publicKey h keys)) (coins.extract 0 32)
      (prepare h coins keys labels) m (sign h keys m) i (outputCodec.encode m)[i.val])
    (fun i => ByteArray.mk ((labels i).get (outputCodec.encode m)[i.val]).toArray)
    (fun i _ => expandLabel_prepared h coins keys labels hcoins m i)
  unfold expand
  rw [hs]
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false,
    prepare_nonce h coins keys labels hcoins, hm]
  congr 1
  simpa only [List.map_map, Function.comp_def] using
    concatenate_labels ((List.finRange 256).map fun i => (labels i).get (outputCodec.encode m)[i.val])

/-- Exact correctness of the protected, public-key-prefixed construction.
This theorem concerns honest evaluation only; it is independent of the
unproved pre-release, post-release and adaptive security reductions. -/
set_option maxRecDepth 4096 in
theorem construction_correct : Correct (wrapped construction) := by
  intro h coins p keys labels m
  change Fin 256 → Pair at labels
  let body := prepare h (ByteArray.mk coins.toArray) keys labels
  let pkbytes := keyCodec.encode (publicKey h keys)
  have hp : pkbytes.size = 2144 := keyCodec_size (publicKey h keys)
  have hprefix : (pkbytes ++ body).extract 0 2144 = pkbytes :=
    ByteArray.extract_append_eq_left hp.symm
  have hbody : (pkbytes ++ body).extract 2144 (pkbytes ++ body).size = body := by
    exact ByteArray.extract_append_eq_right hp.symm ByteArray.size_append
  have hcsize : (ByteArray.mk coins.toArray).size = randomnessBytes := coins.size_toArray
  have hc : 32 ≤ (ByteArray.mk coins.toArray).size := by rw [hcsize]; decide
  change (do
    let pk ← keyCodec.decode ((pkbytes ++ body).extract 0 2144)
    let sig ← keyCodec.decode (keyCodec.encode (sign h keys m))
    if verifies h pk (encodeWord m) sig then
      expand h pk ((pkbytes ++ body).extract 2144 (pkbytes ++ body).size) m sig
    else none) =
      some (pack ((List.finRange 256).map fun i => (labels i).get (outputCodec.encode m)[i.val]))
  simp only [hprefix, pkbytes, keyCodec.decode_encode, Option.bind_some]
  rw [if_pos (sign_verifies h keys m), hbody]
  exact expand_prepared h (ByteArray.mk coins.toArray) keys labels hc m

end WotsLamport.Submission
