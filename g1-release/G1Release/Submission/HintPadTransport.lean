import G1Release.Submission.HintAffineTable
import G1Release.Submission.HintPayloadPrivacy

namespace G1Release.Submission.HintPadTransport

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open GarblingPrize.Protected
open HintAffineTable

abbrev MaskKey := BinaryFieldHint.Key BinaryFieldHint.modulus BinaryFieldHint.remainder

/-- The canonical byte codec is a bijection with all 256-bit integers. -/
def byteNatEquiv : WordBytes ≃ Fin (2 ^ (8 * 32)) :=
  FiniteProbability.bytesFinEquiv 32

theorem byteNatEquiv_val (pad : WordBytes) :
    (byteNatEquiv pad).val = HintCodec.decodeNatLE pad := by
  exact (ByteArithmetic.read_eq pad 32 (Nat.le_refl 32)).trans
    (ByteArithmetic.bitNat_eq pad) |>.symm

theorem fullRange_eq :
    2 ^ (8 * 32) = 2 * BinaryFieldHint.rangeSize BinaryFieldHint.modulus BinaryFieldHint.remainder := by
  rw [rangeSize_eq]
  norm_num [BinaryFieldHint.binaryRange]

/-- Split off the untouched high pad bit; the other 255 bits index the graph. -/
def padCoordinates : WordBytes ≃ Fin 2 × MaskKey :=
  byteNatEquiv.trans ((finCongr fullRange_eq).trans
    (finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _)
      (BinaryFieldHint.keyEquiv _ _).symm)))

theorem padCoordinates_key (pad : WordBytes) :
    (padCoordinates pad).2 = keyFromPad pad := by
  apply (BinaryFieldHint.keyEquiv _ _).injective
  apply Fin.ext
  unfold padCoordinates
  delta finProdFinEquiv
  simp [byteNatEquiv_val, keyFromPad, rangeSize_eq]
  exact congrArg (fun n => n % BinaryFieldHint.binaryRange) (byteNatEquiv_val pad)

def wordEquiv : Fin BinaryFieldHint.modulus ≃ Word where
  toFun value := (value.val : Word)
  invFun value := ⟨value.val, value.val_lt⟩
  left_inv value := by
    apply Fin.ext
    exact ZMod.val_cast_of_lt value.isLt
  right_inv value := ZMod.natCast_zmod_val value

def maskPermutation (difference : Word) : Equiv.Perm (Fin BinaryFieldHint.modulus) :=
  wordEquiv.trans ((Equiv.addRight difference).trans wordEquiv.symm)

theorem wordEquiv_maskPermutation (difference : Word) (value : Fin BinaryFieldHint.modulus) :
    wordEquiv (maskPermutation difference value) = wordEquiv value + difference := by
  simp [maskPermutation]

def padCoinCoordinates : WordBytes × Coin ≃ Fin 2 × (MaskKey × Coin) :=
  (Equiv.prodCongr padCoordinates (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)

theorem padCoinCoordinates_snd (state : WordBytes × Coin) :
    (padCoinCoordinates state).2 = (keyFromPad state.1, state.2) := by
  simp [padCoinCoordinates, padCoordinates_key]

/-- The new sampler transport changes the unused false pad jointly with its
private coin.  The pad's 256th bit is retained as an independent coordinate. -/
noncomputable def padCoinTransport (difference : Word) : Equiv.Perm (WordBytes × Coin) :=
  padCoinCoordinates.trans
    ((Equiv.prodCongr (Equiv.refl (Fin 2))
      (BinaryFieldHint.transport modulus_positive BinaryFieldHint.concrete_remainder.1
        BinaryFieldHint.concrete_remainder.2 (maskPermutation difference))).trans
      padCoinCoordinates.symm)

theorem padCoinTransport_sample (difference : Word) (state : WordBytes × Coin) :
    let target := padCoinTransport difference state
    BinaryFieldHint.sample modulus_positive BinaryFieldHint.concrete_remainder.1
        (keyFromPad target.1) target.2 =
      (maskPermutation difference
          (BinaryFieldHint.sample modulus_positive BinaryFieldHint.concrete_remainder.1
            (keyFromPad state.1) state.2).1,
        (BinaryFieldHint.sample modulus_positive BinaryFieldHint.concrete_remainder.1
          (keyFromPad state.1) state.2).2) := by
  have hcoords := congrArg Prod.snd
    (padCoinCoordinates.apply_symm_apply
      ((Equiv.prodCongr (Equiv.refl (Fin 2))
        (BinaryFieldHint.transport modulus_positive BinaryFieldHint.concrete_remainder.1
          BinaryFieldHint.concrete_remainder.2 (maskPermutation difference)))
        (padCoinCoordinates state)))
  change (padCoinCoordinates (padCoinTransport difference state)).2 = _ at hcoords
  rw [padCoinCoordinates_snd] at hcoords
  change _ = BinaryFieldHint.transport modulus_positive BinaryFieldHint.concrete_remainder.1
    BinaryFieldHint.concrete_remainder.2 (maskPermutation difference)
    (padCoinCoordinates state).2 at hcoords
  rw [padCoinCoordinates_snd] at hcoords
  have hsample := BinaryFieldHint.sample_transport modulus_positive
    BinaryFieldHint.concrete_remainder.1 BinaryFieldHint.concrete_remainder.2
    (maskPermutation difference) (keyFromPad state.1, state.2)
  dsimp only at hsample ⊢
  rw [← hcoords] at hsample
  exact hsample

theorem padCoinTransport_hint (difference : Word) (state : WordBytes × Coin) :
    let target := padCoinTransport difference state
    padHint target.1 target.2 = padHint state.1 state.2 := by
  have h := congrArg (fun output : Fin BinaryFieldHint.modulus × Bool => output.2)
    (padCoinTransport_sample difference state)
  dsimp only at h ⊢
  unfold padHint
  exact h

theorem word_sample (pad : WordBytes) (coin : Coin) :
    wordEquiv (BinaryFieldHint.sample modulus_positive BinaryFieldHint.concrete_remainder.1
      (keyFromPad pad) coin).1 = maskFromPad pad (padHint pad coin) := by
  simp only [wordEquiv, Equiv.coe_fn_mk, maskFromPad, padHint, BinaryFieldHint.sample]

theorem padCoinTransport_mask (difference : Word) (state : WordBytes × Coin) :
    let target := padCoinTransport difference state
    maskFromPad target.1 (padHint target.1 target.2) =
      maskFromPad state.1 (padHint state.1 state.2) + difference := by
  have h := congrArg (fun output : Fin BinaryFieldHint.modulus × Bool => wordEquiv output.1)
    (padCoinTransport_sample difference state)
  dsimp only at h
  rw [wordEquiv_maskPermutation, word_sample, word_sample] at h
  exact h

end G1Release.Submission.HintPadTransport
