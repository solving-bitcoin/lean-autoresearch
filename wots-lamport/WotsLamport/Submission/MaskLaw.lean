import WotsLamport.Submission.CoinEncoding

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

def xorVector {n : Nat} (bytes pad : Bytes n) : Bytes n :=
  Vector.ofFn fun i => bytes[i.val] ^^^ pad[i.val]

theorem xorVector_cancel {n : Nat} (bytes pad : Bytes n) :
    xorVector (xorVector bytes pad) pad = bytes := by
  apply Vector.ext
  intro i hi
  simp [xorVector, UInt8.xor_assoc]

def xorVectorEquiv {n : Nat} (pad : Bytes n) : Bytes n ≃ Bytes n where
  toFun bytes := xorVector bytes pad
  invFun bytes := xorVector bytes pad
  left_inv bytes := xorVector_cancel bytes pad
  right_inv bytes := xorVector_cancel bytes pad

theorem xorVector_bytes {n : Nat} (bytes pad : Bytes n) :
    ByteArray.mk (xorVector bytes pad).toArray =
      xorBytes (ByteArray.mk bytes.toArray) (ByteArray.mk pad.toArray) := by
  apply ByteArray.ext_getElem (by simp)
  intro j hj hj'
  have hjn : j < n := by simpa using hj
  rw [← getElem!_pos (xorBytes _ _) j hj', xorBytes_get _ _ j (by simpa using hjn)]
  rw [getElem!_pos (ByteArray.mk bytes.toArray) j (by simpa using hjn),
    getElem!_pos (ByteArray.mk pad.toArray) j (by simpa using hjn)]
  simp only [ByteArray.getElem_eq_getElem_data, Vector.getElem_toArray,
    xorVector, Vector.getElem_ofFn]

/-- A full finite table of independent uniform pads remains jointly uniform
after XOR with any fixed plaintext table. No marginal-to-joint inference is
used; a single product-space bijection transports the whole event. -/
theorem uniform_masked_table {I : Type} [Fintype I] (n : Nat)
    (plaintext : I → Bytes n) (event : Set (I → Bytes n)) :
    uniformOn (Set.univ : Set (I → Bytes n))
      {pads | (fun i => xorVector (pads i) (plaintext i)) ∈ event} =
        uniformOn (Set.univ : Set (I → Bytes n)) event := by
  let e := Equiv.piCongrRight fun i => xorVectorEquiv (plaintext i)
  exact Shamir.uniform_event_equiv e event

theorem uniform_masked_table_secret_independent {I : Type} [Fintype I] (n : Nat)
    (a b : I → Bytes n) (event : Set (I → Bytes n)) :
    uniformOn (Set.univ : Set (I → Bytes n))
      {pads | (fun i => xorVector (pads i) (a i)) ∈ event} =
    uniformOn (Set.univ : Set (I → Bytes n))
      {pads | (fun i => xorVector (pads i) (b i)) ∈ event} := by
  rw [uniform_masked_table, uniform_masked_table]

end WotsLamport.Submission
