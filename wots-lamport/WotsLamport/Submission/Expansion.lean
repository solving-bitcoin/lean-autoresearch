import WotsLamport.Submission.DecodingBridge
import WotsLamport.Submission.LabelBridge

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

theorem byteArray_bne_self (bytes : ByteArray) : (bytes != bytes) = false := by
  change (!(bytes.data == bytes.data)) = false
  simp

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
  simp only [hlength, hrec, hvalid, hbytes, byteVector_decode_raw, Option.bind_eq_bind, Option.bind_some, Option.map_eq_map, Option.map_some, Option.pure_def,
    bne_self_eq_false, Bool.false_eq_true, ite_false,
    prepare_commitment_slice h coins keys labels hcoins i value, byteArray_bne_self]
  rfl

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
    prepare_nonce h coins keys labels hcoins, hm, Option.bind_eq_bind, Option.bind_some,
    Option.map_eq_map, Option.map_some, Option.pure_def]
  apply congrArg some
  simpa only [List.map_map, Function.comp_def] using
    concatenate_labels ((List.finRange 256).map fun i => (labels i).get (outputCodec.encode m)[i.val])

/-- Expose only the wrapper's monadic plumbing, with abstract byte inputs. -/
theorem wrapped_evaluateBytes_eq (s : Construction) (h : Hash)
    (artifact active : ByteArray) (m : Message) :
    (wrapped s).evaluateBytes h artifact m active =
      (keyCodec.decode (artifact.extract 0 2144)).bind (fun pk =>
        (keyCodec.decode active).bind (fun sig =>
          if verifies h pk (encodeWord m) sig then
            s.expand h pk (artifact.extract 2144 artifact.size) m sig
          else none)) := rfl

/-- Decode two values without simplifying their possibly large continuation. -/
theorem decode_pair {A B : Type} (codec : ByteCodec A) (a b : A)
    (next : A → A → Option B) :
    (codec.decode (codec.encode a)).bind (fun x =>
      (codec.decode (codec.encode b)).bind (fun y => next x y)) = next a b := by
  rw [codec.decode_encode, Option.bind_some, codec.decode_encode, Option.bind_some]

/-- Simplify the wrapper with an abstract body and construction, before
substituting any large executable table definitions. -/
theorem wrapped_evaluate_prefix (s : Construction) (h : Hash) (pk : PublicKey)
    (body : ByteArray) (m : Message) (sig : Signature) :
    (wrapped s).evaluateBytes h (keyCodec.encode pk ++ body) m (signatureBytes sig) =
      if verifies h pk (encodeWord m) sig then s.expand h pk body m sig else none := by
  have size : (keyCodec.encode pk).size = 2144 := keyCodec_size pk
  have prefixBytes : (keyCodec.encode pk ++ body).extract 0 2144 = keyCodec.encode pk :=
    ByteArray.extract_append_eq_left size.symm
  have bodyBytes : (keyCodec.encode pk ++ body).extract 2144
      (keyCodec.encode pk ++ body).size = body :=
    ByteArray.extract_append_eq_right size.symm ByteArray.size_append
  rw [wrapped_evaluateBytes_eq, prefixBytes, bodyBytes]
  exact decode_pair keyCodec pk sig (fun decodedPk decodedSig =>
    if verifies h decodedPk (encodeWord m) decodedSig then
      s.expand h decodedPk body m decodedSig else none)

theorem wrapped_garbleBytes_eq (s : Construction) (h : Hash) (coins : Bytes s.randomnessBytes)
    (p : Unit) (keys : Keys) (labels : Fin 256 → Pair) :
    (wrapped s).garbleBytes h coins p keys labels =
      keyCodec.encode (publicKey h keys) ++ s.prepare h (ByteArray.mk coins.toArray) keys labels := rfl

theorem challenge_reveal_input (h : Hash) (keys : Keys) (m : Message) :
    challenge.inputs.reveal h keys m = signatureBytes (sign h keys m) := rfl

/-- Exact correctness of the protected, public-key-prefixed construction.
This theorem concerns honest evaluation only; it is independent of the
unproved pre-release, post-release and adaptive security reductions. -/
theorem construction_correct : Correct (wrapped construction) := by
  intro h coins p keys labels m
  change (wrapped construction).evaluateBytes h
    ((wrapped construction).garbleBytes h coins p keys labels) m
    (signatureBytes (sign h keys m)) =
    some (pack ((List.finRange 256).map fun i => (labels i).get (outputCodec.encode m)[i.val]))
  rw [wrapped_garbleBytes_eq, wrapped_evaluate_prefix,
    if_pos (sign_verifies h keys m)]
  have hcsize : (ByteArray.mk coins.toArray).size = randomnessBytes := coins.size_toArray
  have hc : 32 ≤ (ByteArray.mk coins.toArray).size := by rw [hcsize]; decide
  exact expand_prepared h (ByteArray.mk coins.toArray) keys labels hc m

end WotsLamport.Submission
