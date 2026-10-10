import WotsLamport.Submission.CoinEncoding

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

/-- Consecutive 32-byte blocks are a bijective reindexing of the coin vector.
Block zero is the nonce; all subsequent blocks are coefficient coins. -/
def byteBlocksEquiv (n : Nat) : Bytes (n*32) ≃ (Fin n → Bytes 32) where
  toFun bytes block := Vector.ofFn fun k => bytes[block.val*32+k.val]'(by
    have hb := block.isLt
    have hk := k.isLt
    omega)
  invFun blocks := Vector.ofFn fun i =>
    (blocks ⟨i.val/32, by have hi := i.isLt; omega⟩)[i.val%32]
  left_inv bytes := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn]
    have he : (i/32)*32+i%32 = i := by omega
    simp only [he]
  right_inv blocks := by
    funext block
    apply Vector.ext
    intro k hk
    simp only [Vector.getElem_ofFn]
    have hd : (block.val*32+k)/32 = block.val := by omega
    have hm : (block.val*32+k)%32 = k := by omega
    have hf : (⟨(block.val*32+k)/32, by have hb := block.isLt; omega⟩ : Fin n) = block := Fin.ext hd
    rw [hf]
    exact congrArg (fun i : Fin 32 => (blocks block)[i.val]) (Fin.ext hm)

theorem byteBlocks_extract (n : Nat) (coins : Bytes (n*32)) (block : Fin n) :
    ByteArray.mk ((byteBlocksEquiv n coins) block).toArray =
      (ByteArray.mk coins.toArray).extract (block.val*32) ((block.val+1)*32) := by
  have hb := block.isLt
  have hs : (ByteArray.mk coins.toArray).size = n*32 := coins.size_toArray
  have he : ((ByteArray.mk coins.toArray).extract (block.val*32) ((block.val+1)*32)).size = 32 := by
    rw [ByteArray.size_extract, hs]
    omega
  apply ByteArray.ext_getElem (by rw [vectorBytes_size, he])
  intro k hk hk'
  rw [ByteArray.getElem_extract]
  simp only [byteBlocksEquiv, ByteArray.getElem_eq_getElem_data,
    Equiv.coe_fn_mk, Vector.getElem_toArray, Vector.getElem_ofFn]

theorem uniform_blocks_product (n : Nat) :
    (uniformOn (Set.univ : Set (Fin n → Bytes 32))) =
      Measure.pi (fun _ : Fin n => uniformOn (Set.univ : Set (Bytes 32))) := by
  simpa using (uniformOn_pi (f := fun _ : Fin n => (Set.univ : Set (Bytes 32))))

/-- The distribution of the entire block table is the product of uniform
32-byte laws, including the nonce and all allocated coefficient blocks. -/
theorem uniform_coin_blocks (n : Nat) (event : Set (Fin n → Bytes 32)) :
    uniformOn (Set.univ : Set (Bytes (n*32))) ((byteBlocksEquiv n) ⁻¹' event) =
      (Measure.pi (fun _ : Fin n => uniformOn (Set.univ : Set (Bytes 32)))) event := by
  rw [Shamir.uniform_event_equiv (byteBlocksEquiv n), uniform_blocks_product]

def coefficientBlocks (coins : Bytes randomnessBytes) : Fin (coefficientCount+1) → Bytes 32 :=
  byteBlocksEquiv (coefficientCount+1) coins

def coefficientBlock (coins : Bytes randomnessBytes) (block : Fin coefficientCount) : Bytes 32 :=
  coefficientBlocks coins ⟨block.val+1, Nat.succ_lt_succ block.isLt⟩

theorem coefficient_block_read (coins : Bytes randomnessBytes) (block : Fin coefficientCount) :
    readLE (ByteArray.mk (coefficientBlock coins block).toArray) 0 32 =
      readLE (ByteArray.mk coins.toArray) (32+block.val*32) 32 := by
  have hb := block.isLt
  have hs : (ByteArray.mk coins.toArray).size = randomnessBytes := coins.size_toArray
  have he := byteBlocks_extract (coefficientCount+1) coins
    ⟨block.val+1, by omega⟩
  change readLE (ByteArray.mk ((byteBlocksEquiv (coefficientCount+1) coins)
    ⟨block.val+1, by omega⟩).toArray) 0 32 = _
  rw [he]
  have hstart : (block.val+1)*32 = 32+block.val*32 := by omega
  have hstop : (block.val+1+1)*32 = (32+block.val*32)+32 := by omega
  rw [hstart, hstop]
  have hbound : (32+block.val*32)+32 ≤ randomnessBytes := by
    change (32+block.val*32)+32 ≤ 32+coefficientCount*32
    omega
  exact readLE_extract _ _ _ (by rw [hs]; exact hbound)

end WotsLamport.Submission
