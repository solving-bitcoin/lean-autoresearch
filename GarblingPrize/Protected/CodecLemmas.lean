import GarblingPrize.Protected.Codec
import Batteries.Data.Nat.Lemmas
import Init.Data.Nat.Bitwise.Lemmas

namespace GarblingPrize.Protected.Codec

/-!
# Arithmetic correctness of fixed-width integer codecs

The executable decoder folds whole little-endian bytes.  These lemmas recover
the usual fixed-width integer semantics against `natLE`.
-/

private theorem u8_toNat_ofNat (value : Nat) :
    (UInt8.ofNat value).toNat = value % 256 := by
  simp [UInt8.toNat_ofNat']

private theorem decodeNatLE_zero (bytes : Bytes 0) :
    decodeNatLE bytes = 0 := by
  simp [decodeNatLE]

private theorem decodeNatLE_succ (bytes : Bytes (width + 1)) :
    decodeNatLE bytes =
      Fin.foldl width
          (fun acc i =>
            acc + (bytes.get i.castSucc).toNat * (1 <<< (8 * i.val))) 0 +
        (bytes.get (Fin.last width)).toNat * (1 <<< (8 * width)) := by
  simp only [decodeNatLE]
  rw [Fin.foldl_succ_last]
  simp [Fin.val_castSucc, Fin.val_last]

private theorem natLE_get (width value : Nat) (i : Fin width) :
    (natLE width value).get i =
      UInt8.ofNat (value / 2 ^ (8 * i.val)) := by
  simp [natLE, Bytes.ofFn, Vector.get_eq_getElem, Nat.shiftRight_eq_div_pow]

private theorem natLE_prefix (width value : Nat) (i : Fin width) :
    (natLE (width + 1) value).get i.castSucc =
      (natLE width value).get i := by
  simp [natLE_get, Fin.val_castSucc]

private theorem decodeNatLE_natLE_succ (width value : Nat) :
    decodeNatLE (natLE (width + 1) value) =
      decodeNatLE (natLE width value) +
        ((value / 2 ^ (8 * width)) % 256) * 2 ^ (8 * width) := by
  have hprefix :
      Fin.foldl width
          (fun acc i =>
            acc +
              ((natLE (width + 1) value).get i.castSucc).toNat *
                (1 <<< (8 * i.val))) 0 =
        decodeNatLE (natLE width value) := by
    simp only [decodeNatLE]
    refine congrArg (fun f => Fin.foldl width f 0) ?_
    funext acc i
    rw [natLE_prefix]
  rw [decodeNatLE_succ, hprefix, natLE_get, Fin.val_last, u8_toNat_ofNat]
  simp [Nat.shiftLeft_eq]

private theorem mod_pow_succ_byte (value width : Nat) :
    value % 2 ^ (8 * (width + 1)) =
      value % 2 ^ (8 * width) +
        ((value / 2 ^ (8 * width)) % 256) * 2 ^ (8 * width) := by
  have hpow : 2 ^ (8 * (width + 1)) = 2 ^ (8 * width) * 256 := by
    rw [show 8 * (width + 1) = 8 * width + 8 by omega, Nat.pow_add]
  rw [hpow, Nat.mod_mul]
  ac_rfl

theorem decodeNatLE_natLE_mod (width value : Nat) :
    decodeNatLE (natLE width value) = value % 2 ^ (8 * width) := by
  induction width with
  | zero =>
      simp [decodeNatLE_zero, Nat.mod_one]
  | succ width ih =>
      rw [decodeNatLE_natLE_succ, ih, mod_pow_succ_byte]

theorem decodeNatLE_natLE_of_lt (width value : Nat)
    (h : value < 2 ^ (8 * width)) :
    decodeNatLE (natLE width value) = value := by
  rw [decodeNatLE_natLE_mod, Nat.mod_eq_of_lt h]

/-- Recover each source byte from the bit-major little-endian natural. -/
theorem natLE_ofBits_byteBitsLE (bytes : Bytes width) :
    natLE width (Nat.ofBits (byteBitsLE bytes)) = bytes := by
  apply Vector.ext
  intro i hi
  simp only [natLE, Bytes.ofFn, Vector.getElem_ofFn]
  refine UInt8.toNat_inj.1 ?_
  rw [u8_toNat_ofNat]
  refine Nat.eq_of_testBit_eq fun b => ?_
  if hb : b < 8 then
    have hidx : 8 * i + b < 8 * width := by omega
    have hdiv : (8 * i + b) / 8 = i := by omega
    have hmod : (8 * i + b) % 8 = b := by omega
    rw [Nat.shiftRight_eq_div_pow, show (256 : Nat) = 2 ^ 8 by decide,
      Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.testBit_ofBits]
    simp [hb, byteBitsLE, show b + 8 * i = 8 * i + b by omega, hdiv, hmod,
      Vector.get_eq_getElem]
    rw [dif_pos hidx, BitVec.getElem_eq_testBit_toNat, UInt8.toNat_toBitVec]
  else
    have hbyte : bytes[i].toNat < 2 ^ 8 :=
      Nat.lt_of_lt_of_le bytes[i].toNat_lt_size (by decide)
    have hge : 8 ≤ b := Nat.ge_of_not_lt hb
    rw [show (256 : Nat) = 2 ^ 8 by decide, Nat.testBit_mod_two_pow]
    simp [hb, Nat.testBit_lt_two_pow
      (Nat.lt_of_lt_of_le hbyte (Nat.pow_le_pow_right (by decide) hge))]

/-- The byte fold agrees with the historical bit-major `Nat.ofBits` layout. -/
theorem decodeNatLE_eq_ofBits (bytes : Bytes width) :
    decodeNatLE bytes = decodeNatLEBits bytes := by
  unfold decodeNatLEBits
  have hbound : Nat.ofBits (byteBitsLE bytes) < 2 ^ (8 * width) :=
    Nat.ofBits_lt_two_pow _
  calc
    decodeNatLE bytes =
        decodeNatLE (natLE width (Nat.ofBits (byteBitsLE bytes))) := by
      rw [natLE_ofBits_byteBitsLE]
    _ = Nat.ofBits (byteBitsLE bytes) :=
      decodeNatLE_natLE_of_lt _ _ hbound

end GarblingPrize.Protected.Codec
