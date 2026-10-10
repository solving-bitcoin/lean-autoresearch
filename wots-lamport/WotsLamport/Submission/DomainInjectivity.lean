import WotsLamport.Submission.DomainSeparation

namespace WotsLamport.Submission
open SecretRelease

theorem read_writeLE_one (n : Nat) (hn : n < 256) : readLE (writeLE 1 n) 0 1 = n := by
  change (writeLE 1 n)[0]!.toNat + 256*0 = n
  rw [writeLE_get 1 n 0 (by decide)]
  simp only [Nat.pow_zero, Nat.div_one, UInt8.toNat_ofNat', Nat.mul_zero, Nat.add_zero]
  exact Nat.mod_eq_of_lt hn

theorem read_writeLE_two (n : Nat) (hn : n < 65536) : readLE (writeLE 2 n) 0 2 = n := by
  change (writeLE 2 n)[0]!.toNat + 256*((writeLE 2 n)[1]!.toNat + 256*0) = n
  rw [writeLE_get 2 n 0 (by decide), writeLE_get 2 n 1 (by decide)]
  simp only [Nat.reducePow, Nat.div_one, UInt8.toNat_ofNat', Nat.mul_zero, Nat.add_zero]
  omega

theorem writeLE_two_injective {a b : Nat} (ha : a < 65536) (hb : b < 65536)
    (he : writeLE 2 a = writeLE 2 b) : a = b := by
  have h := congrArg (fun bytes => readLE bytes 0 2) he
  simpa only [read_writeLE_two a ha, read_writeLE_two b hb] using h

theorem writeLE_bool_injective {a b : Bool}
    (he : writeLE 1 (if a then 1 else 0) = writeLE 1 (if b then 1 else 0)) : a = b := by
  have h := congrArg (fun bytes => readLE bytes 0 1) he
  have ha : (if a then 1 else 0) < (256 : Nat) := by cases a <;> decide
  have hb : (if b then 1 else 0) < (256 : Nat) := by cases b <;> decide
  rw [read_writeLE_one _ ha, read_writeLE_one _ hb] at h
  cases a <;> cases b <;> simp_all

theorem domain_injective (tag : String) (pk nonce : ByteArray)
    {wire wire' : Fin 256} {value value' : Bool}
    (he : domain tag pk nonce wire.val value = domain tag pk nonce wire'.val value') :
    wire = wire' ∧ value = value' := by
  unfold domain at he
  obtain ⟨hleft, hvalue⟩ :=
    (ByteArray.append_eq_append_iff_of_size_eq_right (by simp only [writeLE_size])).mp he
  obtain ⟨_, hwire⟩ :=
    (ByteArray.append_eq_append_iff_of_size_eq_right (by simp only [writeLE_size])).mp hleft
  exact ⟨Fin.ext (writeLE_two_injective (by have := wire.isLt; omega)
    (by have := wire'.isLt; omega) hwire), writeLE_bool_injective hvalue⟩

/-- All role-local coordinates are retained by the actual mask serialization.
The slot point lies in 1..1984 and the two mask blocks have distinct encodings. -/
theorem maskQuery_injective (pk nonce : ByteArray)
    {wire wire' : Fin 256} {value value' : Bool} {point point' : Fin 1984}
    {node node' : Label} {block block' : Bool}
    (he : maskQuery pk nonce wire.val value (point.val+1) node (if block then 1 else 0) =
      maskQuery pk nonce wire'.val value' (point'.val+1) node' (if block' then 1 else 0)) :
    wire = wire' ∧ value = value' ∧ point = point' ∧ node = node' ∧ block = block' := by
  unfold maskQuery at he
  obtain ⟨hleft, hblock⟩ :=
    (ByteArray.append_eq_append_iff_of_size_eq_right (by simp only [writeLE_size])).mp he
  obtain ⟨hleft, hnode⟩ :=
    (ByteArray.append_eq_append_iff_of_size_eq_right (by simp only [vectorBytes_size])).mp hleft
  obtain ⟨hdomain, hpoint⟩ :=
    (ByteArray.append_eq_append_iff_of_size_eq_right (by simp only [writeLE_size])).mp hleft
  obtain ⟨hwire, hvalue⟩ := domain_injective _ pk nonce hdomain
  have hp := writeLE_two_injective (by have := point.isLt; omega)
    (by have := point'.isLt; omega) hpoint
  have hn : node = node' := Vector.toArray_inj.mp (congrArg ByteArray.data hnode)
  exact ⟨hwire, hvalue, Fin.ext (by omega), hn, writeLE_bool_injective hblock⟩

theorem commitmentQuery_injective (pk nonce : ByteArray)
    {wire wire' : Fin 256} {value value' : Bool} {label label' : Label}
    (he : commitmentQuery pk nonce wire.val value label =
      commitmentQuery pk nonce wire'.val value' label') :
    wire = wire' ∧ value = value' ∧ label = label' := by
  unfold commitmentQuery at he
  obtain ⟨hdomain, hlabel⟩ :=
    (ByteArray.append_eq_append_iff_of_size_eq_right (by simp only [vectorBytes_size])).mp he
  obtain ⟨hwire, hvalue⟩ := domain_injective _ pk nonce hdomain
  exact ⟨hwire, hvalue, Vector.toArray_inj.mp (congrArg ByteArray.data hlabel)⟩

end WotsLamport.Submission
