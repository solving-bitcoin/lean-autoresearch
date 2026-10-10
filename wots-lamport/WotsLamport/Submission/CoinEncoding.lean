import WotsLamport.Submission.ByteBridge
import WotsLamport.Submission.SamplerLaw
import WotsLamport.Submission.ShamirLaw
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Fintype.EquivFin

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

theorem uniform_map_equiv {A B : Type} [Finite A] [Finite B]
    [MeasurableSpace A] [MeasurableSpace B]
    [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B] (e : A ≃ B) :
    (uniformOn (Set.univ : Set A)).map e = uniformOn (Set.univ : Set B) := by
  apply Measure.ext
  intro event he
  rw [Measure.map_apply Measurable.of_discrete he, Shamir.uniform_event_equiv e]

def byteDigits {n : Nat} (bytes : Bytes n) : List Nat := bytes.toList.map UInt8.toNat

theorem byteDigits_length {n : Nat} (bytes : Bytes n) : (byteDigits bytes).length = n := by
  simp [byteDigits]

theorem byteDigits_bounded {n : Nat} (bytes : Bytes n) :
    ∀ d ∈ byteDigits bytes, d < 256 := by
  intro d hd
  obtain ⟨byte, _, rfl⟩ := List.mem_map.mp hd
  exact UInt8.toNat_lt_size byte

theorem range_byteDigits {n : Nat} (bytes : Bytes n) :
    (List.range n).map (fun j => (ByteArray.mk bytes.toArray)[j]!.toNat) = byteDigits bytes := by
  apply List.ext_getElem (by simp [byteDigits])
  intro j hj hj'
  have hjn : j < n := by simpa only [List.length_map, List.length_range] using hj
  simp only [List.getElem_map, List.getElem_range, byteDigits, Vector.getElem_toList]
  rw [getElem!_pos (ByteArray.mk bytes.toArray) j (by rw [vectorBytes_size]; exact hjn)]
  rfl

theorem readLE_ofDigits {n : Nat} (bytes : Bytes n) :
    readLE (ByteArray.mk bytes.toArray) 0 n = Nat.ofDigits 256 (byteDigits bytes) := by
  rw [Nat.ofDigits_eq_foldr, ← range_byteDigits bytes, List.foldr_map]
  simp only [readLE, Nat.zero_add, Nat.cast_id]

def bytesInteger {n : Nat} (bytes : Bytes n) : Fin (256^n) :=
  ⟨Nat.ofDigits 256 (byteDigits bytes), by
    simpa only [byteDigits_length] using
      Nat.ofDigits_lt_base_pow_length (by decide : 1 < 256) (byteDigits_bounded bytes)⟩

theorem bytesInteger_injective (n : Nat) : Function.Injective (bytesInteger (n := n)) := by
  intro a b he
  have hd : byteDigits a = byteDigits b := Nat.ofDigits_inj_of_len_eq
    (by decide : 1 < 256) (by rw [byteDigits_length, byteDigits_length])
    (byteDigits_bounded a) (byteDigits_bounded b) (congrArg Fin.val he)
  apply Vector.toList_inj.mp
  exact (List.map_inj_right (fun x y h => UInt8.toNat_inj.mp h)).mp hd

def bytesFunctionEquiv (n : Nat) : Bytes n ≃ (Fin n → Fin 256) where
  toFun bytes := fun i => (bytes.get i).toFin
  invFun f := Vector.ofFn fun i => UInt8.ofNat (f i).val
  left_inv bytes := by
    apply Vector.ext
    intro i hi
    simp [Vector.get_eq_getElem]
  right_inv f := by
    funext i
    apply Fin.ext
    simp only [Vector.get_eq_getElem, Vector.getElem_ofFn, UInt8.toFin_val]
    exact UInt8.toNat_ofNat_of_lt' (f i).isLt

theorem bytes_card (n : Nat) [Fintype (Bytes n)] : Fintype.card (Bytes n) = 256^n := by
  simpa using Fintype.card_congr (bytesFunctionEquiv n)

/-- A byte vector's ordinary little-endian integer encoding is a bijection,
not an arbitrarily chosen enumeration of the finite sample space. -/
noncomputable def byteIntegerEquiv (n : Nat) : Bytes n ≃ Fin (256^n) := by
  letI := Fintype.ofFinite (Bytes n)
  exact Equiv.ofBijective bytesInteger
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨bytesInteger_injective n, by simpa using bytes_card n⟩)

noncomputable def coinBlockEquiv : Bytes 32 ≃ Fin Sampler.sampleSize :=
  (byteIntegerEquiv 32).trans (finCongr (by norm_num [Sampler.sampleSize]))

theorem coinBlockEquiv_value (bytes : Bytes 32) :
    (coinBlockEquiv bytes).val = readLE (ByteArray.mk bytes.toArray) 0 32 := by
  change Nat.ofDigits 256 (byteDigits bytes) = _
  exact (readLE_ofDigits bytes).symm

local instance (n : Nat) : MeasurableSpace (Fin n) := ⊤

/-- Exact law of the implementation's 32-byte modular coefficient decoder
on one uniformly sampled byte block. Independence of all selected blocks and
the joint distance bound remain separate obligations. -/
theorem uniform_coinBlock_residue (r : Fin 65537) :
    uniformOn (Set.univ : Set (Bytes 32))
      {bytes | readLE (ByteArray.mk bytes.toArray) 0 32 % 65537 = r.val} =
      (Sampler.residueCount r : ENNReal) / Sampler.sampleSize := by
  have hevent : {bytes : Bytes 32 | readLE (ByteArray.mk bytes.toArray) 0 32 % 65537 = r.val} =
      coinBlockEquiv ⁻¹' {n : Fin Sampler.sampleSize | n.val % 65537 = r.val} := by
    ext bytes
    simp only [Set.mem_setOf_eq, Set.mem_preimage, coinBlockEquiv_value]
  rw [hevent, Shamir.uniform_event_equiv coinBlockEquiv]
  exact Sampler.residue_probability r

end WotsLamport.Submission
