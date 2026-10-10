import WotsLamport.Submission.ByteBridge

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

theorem extract_append_left_of_le (a b : ByteArray) (start stop : Nat)
    (hstop : stop ≤ a.size) : (a ++ b).extract start stop = a.extract start stop := by
  rw [ByteArray.extract_append]
  have hz : stop-a.size = 0 := Nat.sub_eq_zero_of_le hstop
  simp [hz]

/-- A subrange can be read either directly or through its containing block. -/
theorem extract_within_block (a : ByteArray) (base width start stop : Nat)
    (hstop : stop ≤ width) :
    (a.extract base (base+width)).extract start stop = a.extract (base+start) (base+stop) := by
  rw [ByteArray.extract_extract, Nat.min_eq_left (by omega)]

theorem prepare_nonce (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) (hcoins : 32 ≤ coins.size) :
    (prepare h coins keys labels).extract 0 32 = coins.extract 0 32 := by
  have hn : (coins.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract]
    omega
  unfold prepare
  rw [ByteArray.append_assoc, ByteArray.extract_append_eq_left hn.symm]

/-- The exact wire block occupies the same offset for all keys, labels,
oracle functions and sufficiently long coin strings. -/
theorem prepare_wire_block (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) (hcoins : 32 ≤ coins.size) (i : Fin 256) :
    (prepare h coins keys labels).extract
      (32+512*32+i.val*((1984+1982)*48))
      (32+512*32+(i.val+1)*((1984+1982)*48)) =
      labelTable h coins (keyCodec.encode (publicKey h keys)) (coins.extract 0 32)
        keys i false ((labels i).get false) ++
      labelTable h coins (keyCodec.encode (publicKey h keys)) (coins.extract 0 32)
        keys i true ((labels i).get true) := by
  let nonce := coins.extract 0 32
  let pk := keyCodec.encode (publicKey h keys)
  let commitments := concatenate ((List.finRange 256).map fun j =>
    ByteArray.mk (commitment h pk nonce j.val false ((labels j).get false)).toArray ++
    ByteArray.mk (commitment h pk nonce j.val true ((labels j).get true)).toArray)
  let rows := (List.finRange 256).map fun j =>
    labelTable h coins pk nonce keys j false ((labels j).get false) ++
    labelTable h coins pk nonce keys j true ((labels j).get true)
  have hn : nonce.size = 32 := by
    dsimp [nonce]
    rw [ByteArray.size_extract]
    omega
  have hc : commitments.size = 512*32 := by
    dsimp only [commitments]
    rw [concatenate_map_size _ _ 64 (by
      intro j _; simp only [ByteArray.size_append, vectorBytes_size])]
    rfl
  have hp : (nonce ++ commitments).size = 32+512*32 := by
    rw [ByteArray.size_append, hn, hc]
  have hs : ∀ row ∈ rows, row.size = (1984+1982)*48 := by
    intro row hr
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
    simp [ByteArray.size_append, labelTable_size, slots_length]
  change ((nonce ++ commitments) ++ concatenate rows).extract _ _ = _
  rw [← hp, ByteArray.extract_append_size_add,
    concatenate_extract rows ((1984+1982)*48) hs i.val (by simpa [rows] using i.isLt)]
  simp only [rows, List.getElem_map, List.getElem_finRange]

theorem prepare_share_slice (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) (hcoins : 32 ≤ coins.size)
    (i : Fin 256) (value : Bool) (index : Nat) (hi : index < (slots i value).length) :
    (prepare h coins keys labels).extract
      (32+512*32+(i.val*(1984+1982)+(if value then 1984 else 0))*48+index*48)
      (32+512*32+(i.val*(1984+1982)+(if value then 1984 else 0))*48+(index+1)*48) =
      (labelTable h coins (keyCodec.encode (publicKey h keys)) (coins.extract 0 32)
        keys i value ((labels i).get value)).extract (index*48) ((index+1)*48) := by
  let base := 32+512*32+i.val*((1984+1982)*48)
  let left := labelTable h coins (keyCodec.encode (publicKey h keys)) (coins.extract 0 32)
    keys i false ((labels i).get false)
  let right := labelTable h coins (keyCodec.encode (publicKey h keys)) (coins.extract 0 32)
    keys i true ((labels i).get true)
  have hl : left.size = 1984*48 := by simp [left, labelTable_size, slots_length]
  have hw : (prepare h coins keys labels).extract base (base+(1984+1982)*48) = left ++ right := by
    convert prepare_wire_block h coins keys labels hcoins i using 1 <;> dsimp [base] <;> omega
  have hb : (if value then 1984 else 0)*48+(index+1)*48 ≤ (1984+1982)*48 := by
    rw [slots_length] at hi
    cases value <;> simp only [Bool.false_eq_true, ite_false, ite_true] at * <;> omega
  have hs := congrArg (fun bytes : ByteArray => bytes.extract
    ((if value then 1984 else 0)*48+index*48)
    ((if value then 1984 else 0)*48+(index+1)*48)) hw
  rw [extract_within_block _ _ _ _ _ hb] at hs
  cases value with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Nat.zero_mul, Nat.zero_add] at hs ⊢
    rw [extract_append_left_of_le left right _ _ (by
      rw [hl]
      rw [slots_length] at hi
      simp only [Bool.false_eq_true, ite_false] at hi
      omega)] at hs
    convert hs using 1 <;> dsimp [base] <;> omega
  | true =>
    simp only [ite_true] at hs ⊢
    rw [← hl, ByteArray.extract_append_size_add] at hs
    convert hs using 1 <;> dsimp [base] <;> omega

end WotsLamport.Submission
