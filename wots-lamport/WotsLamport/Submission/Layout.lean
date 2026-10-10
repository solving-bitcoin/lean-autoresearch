import WotsLamport.Submission.Geometry

/-! Structural size obligations for the actual serializers. The final bound
quantifies over every hash, coin string, WOTS key and distinct label table. -/
namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

@[simp] theorem writeLE_size (length n : Nat) : (writeLE length n).size = length := by
  simp [writeLE, ByteArray.size]

@[simp] theorem xorBytes_size (a b : ByteArray) : (xorBytes a b).size = a.size := by
  simp only [xorBytes, ByteArray.size, Array.size_map, List.size_toArray, List.length_range]

theorem mask_size (h : Hash) (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) : (mask h pk nonce wire value point node).size = 48 := by
  simp [mask, ByteArray.size_append, ByteArray.size_extract, ByteArray.size]

theorem polynomial_length (coins : ByteArray) (label : Label) (wire limb : Nat)
    (value : Bool) : (polynomial coins label wire limb value).length = threshold value := by
  simp [polynomial]

theorem target_maximum (i : Fin 256) : maximum (targetChain i) = 15 := by
  have hi : (targetChain i).val < 64 := (bitChain i).isLt
  simp [maximum, show (targetChain i).val ≠ 64 by omega,
    show (targetChain i).val ≠ 65 by omega]

theorem target_weight (i : Fin 256) : weight (targetChain i) = 1 := by
  have hi : (targetChain i).val < 64 := (bitChain i).isLt
  simp [weight, show (targetChain i).val ≠ 65 by omega,
    show (targetChain i).val ≠ 66 by omega]

set_option maxRecDepth 4096 in
/-- Only eight tiny nibble cases are reduced in the kernel. The 67-chain
aggregation below is symbolic and does not materialize the share lists. -/
private theorem nibble_multiplicity_sum (r : Fin 4) (value : Bool) :
    ((List.range 15).map fun k =>
      (multiplicity 1 (fun d => d.testBit r.val == value) k).toNat).sum =
      if value then 14 else 16 := by
  revert r value
  decide +kernel

theorem chain_slot_count (i : Fin 256) (value : Bool) (j : Fin 67) :
    ((List.range (maximum j)).map fun k =>
      if j = targetChain i then (multiplicity (weight j) (holds i value) k).toNat
      else weight j).sum =
      if j = targetChain i then (if value then 14 else 16) else weight j * maximum j := by
  by_cases h : j = targetChain i
  · subst j
    simpa [target_maximum, target_weight, holds, digitBit] using
      nibble_multiplicity_sum ⟨bitInNibble i, Nat.mod_lt i.val (by decide)⟩ value
  · simp [h, Nat.mul_comm]

theorem slots_length (i : Fin 256) (value : Bool) :
    (slots i value).length = if value then 1982 else 1984 := by
  have hs : (slots i value).length =
      ∑ j : Fin 67, if j = targetChain i then (if value then 14 else 16)
        else weight j * maximum j := by
    simp only [slots, List.length_flatMap, List.length_replicate]
    rw [← Fin.sum_univ_def]
    apply Finset.sum_congr rfl
    intro j _
    exact chain_slot_count i value j
  have h15 : (∑ j : Fin 67, if j = targetChain i then 15 else 0) = 15 := by simp
  have hv : (∑ j : Fin 67, if j = targetChain i then (if value then 14 else 16) else 0) =
      (if value then 14 else 16) := by simp
  have hp : weight (targetChain i) * maximum (targetChain i) = 15 := by
    rw [target_weight, target_maximum]
  have he : (∑ j : Fin 67, if j = targetChain i then (if value then 14 else 16)
        else weight j * maximum j) + 15 =
      (∑ j : Fin 67, weight j * maximum j) + (if value then 14 else 16) := by
    calc
      _ = (∑ j : Fin 67, if j = targetChain i then (if value then 14 else 16)
          else weight j * maximum j) + (∑ j : Fin 67, if j = targetChain i then 15 else 0) := by rw [h15]
      _ = ∑ j : Fin 67, ((if j = targetChain i then (if value then 14 else 16)
          else weight j * maximum j) + (if j = targetChain i then 15 else 0)) := by
        rw [Finset.sum_add_distrib]
      _ = ∑ j : Fin 67, (weight j * maximum j +
          (if j = targetChain i then (if value then 14 else 16) else 0)) := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = targetChain i
        · subst j; simp [hp, Nat.add_comm]
        · simp [h]
      _ = _ := by rw [Finset.sum_add_distrib, hv]
  rw [maximum_weighted_sum] at he
  rw [hs]
  cases value <;> simp at he ⊢ <;> omega

theorem serialized_layout_arithmetic :
    2144 + 32 + 512*32 + 256*(1984+1982)*48 = artifactBytes := by rfl

theorem append_fold_size (parts : List ByteArray) (initial : ByteArray) :
    (parts.foldl (fun acc part => acc ++ part) initial).size =
      initial.size + (parts.map ByteArray.size).sum := by
  induction parts generalizing initial with
  | nil => simp
  | cons part parts ih =>
    simp only [List.foldl_cons, ih, ByteArray.size_append, List.map_cons, List.sum_cons]
    omega

theorem concatenate_size (parts : List ByteArray) :
    (concatenate parts).size = (parts.map ByteArray.size).sum := by
  rw [concatenate, append_fold_size]
  simp only [ByteArray.size_empty, Nat.zero_add]

theorem concatenate_map_size {A : Type} (xs : List A) (f : A → ByteArray) (n : Nat) :
    (∀ x ∈ xs, (f x).size = n) → (concatenate (xs.map f)).size = xs.length*n := by
  rw [concatenate_size]
  simp only [List.map_map]
  induction xs with
  | nil => intro _; simp
  | cons x xs ih =>
    intro hf
    have hx := hf x (by simp)
    have ht := ih (fun y hy => hf y (by simp [hy]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Function.comp_apply] at *
    rw [hx, ht]
    simp [Nat.add_mul, Nat.add_comm]

theorem labelTable_size (h : Hash) (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label) :
    (labelTable h coins pk nonce keys i value label).size = (slots i value).length*48 := by
  unfold labelTable
  rw [concatenate_map_size _ _ 48]
  · simp
  · intro point _
    rcases point with ⟨⟨j, k⟩, index⟩
    rw [xorBytes_size, concatenate_map_size _ _ 3]
    · simp
    · intro p _; exact writeLE_size _ _

theorem vectorBytes_size {n : Nat} (v : Bytes n) :
    (ByteArray.mk v.toArray).size = n := by
  exact v.size_toArray

theorem prepare_size (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) :
    (prepare h coins keys labels).size = (coins.extract 0 32).size +
      512*32 + 256*(1984+1982)*48 := by
  let nonce := coins.extract 0 32
  let pk := keyCodec.encode (publicKey h keys)
  have hc := concatenate_map_size (List.finRange 256)
    (fun i => ByteArray.mk (commitment h pk nonce i.val false ((labels i).get false)).toArray ++
      ByteArray.mk (commitment h pk nonce i.val true ((labels i).get true)).toArray)
    64 (by intro i _; simp only [ByteArray.size_append, vectorBytes_size])
  have ht := concatenate_map_size (List.finRange 256)
    (fun i => labelTable h coins pk nonce keys i false ((labels i).get false) ++
      labelTable h coins pk nonce keys i true ((labels i).get true))
    ((1984+1982)*48) (by intro i _; simp [labelTable_size, slots_length])
  dsimp only [pk, nonce] at hc ht
  unfold prepare
  rw [ByteArray.size_append, ByteArray.size_append, hc, ht]
  simp

theorem codecBytes_size {A : Type} (c : Codec A) (a : A) :
    (c.bytes.encode a).size = (c.width+7)/8 := by
  change (packBits (c.encode a)).size = (c.width+7)/8
  simp [packBits, ByteArray.size]

theorem keyCodec_size (keys : Keys) : (keyCodec.encode keys).size = 2144 := by
  change ((Codec.pi 67 (Codec.byteVector 32)).bytes.encode keys).size = 2144
  rw [codecBytes_size]
  rfl

/-- The claimed serialized byte bound, including the mandatory public key.
This does not establish functional correctness or either security game. -/
theorem artifact_bound : ArtifactBound (wrapped construction) artifactBytes := by
  intro h coins p keys labels
  change Fin 256 → Pair at labels
  change (keyCodec.encode (publicKey h keys) ++
    prepare h ⟨coins.toArray⟩ keys labels).size ≤ artifactBytes
  rw [ByteArray.size_append, keyCodec_size]
  rw [prepare_size h ⟨coins.toArray⟩ keys labels]
  have hc : (ByteArray.mk coins.toArray).size = randomnessBytes := coins.size_toArray
  rw [ByteArray.size_extract, hc]
  decide

end WotsLamport.Submission
