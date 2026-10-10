import WotsLamport.Submission.Sharing

/-! Structural size obligations for the actual serializers. The final bound
quantifies over every hash, coin string, WOTS key and distinct label table. -/
namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

@[simp] theorem writeLE_size (length n : Nat) : (writeLE length n).size = length := by
  simp [writeLE, ByteArray.size]

@[simp] theorem xorBytes_size (a b : ByteArray) : (xorBytes a b).size = a.size := by
  simp [xorBytes, ByteArray.size]

theorem mask_size (h : Hash) (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) : (mask h pk nonce wire value point node).size = 48 := by
  simp [mask, ByteArray.size_append, ByteArray.size_extract, ByteArray.size]

theorem polynomial_length (coins : ByteArray) (label : Label) (wire limb : Nat)
    (value : Bool) : (polynomial coins label wire limb value).length = threshold value := by
  simp [polynomial]

/-- Finite geometry only: this kernel reduction has no cryptographic inputs.
Unlike native_decide it does not add an executable-code axiom to the proof. -/
set_option maxRecDepth 8192 in
set_option maxHeartbeats 5000000 in
theorem slots_length (i : Fin 256) (value : Bool) :
    (slots i value).length = if value then 1982 else 1984 := by
  revert i value
  decide

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
  simp [concatenate, append_fold_size, ByteArray.size]

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
    rw [xorBytes_size, concatenate_map_size _ _ 3]
    · simp
    · intro p _; exact writeLE_size _ _

theorem prepare_size (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : challenge.outputs.Keys) :
    (prepare h coins keys labels).size = (coins.extract 0 32).size +
      512*32 + 256*(1984+1982)*48 := by
  unfold prepare
  rw [ByteArray.size_append, ByteArray.size_append]
  rw [concatenate_map_size _ _ 64 (by
    intro i _; simp [ByteArray.size_append, ByteArray.size])]
  rw [concatenate_map_size _ _ ((1984+1982)*48) (by
    intro i _; simp [ByteArray.size_append, labelTable_size, slots_length])]
  simp

theorem keyCodec_size (keys : Keys) : (keyCodec.encode keys).size = 2144 := by
  simp [keyCodec, Codec.bytes, ByteCodec.checked, packBits, ByteArray.size,
    Codec.pi, Codec.byteVector]

/-- The claimed serialized byte bound, including the mandatory public key.
This does not establish functional correctness or either security game. -/
theorem artifact_bound : ArtifactBound (wrapped construction) artifactBytes := by
  intro h coins p keys labels
  change (keyCodec.encode (publicKey h keys) ++
    prepare h ⟨coins.toArray⟩ keys labels).size ≤ artifactBytes
  rw [ByteArray.size_append, keyCodec_size, prepare_size]
  simp [ByteArray.size_extract, ByteArray.size, construction, randomnessBytes,
    coefficientCount, artifactBytes, bodyBytes]

end WotsLamport.Submission
