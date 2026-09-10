import G1Release.Submission.HintPadTransport
import G1Release.Submission.DutyFreeModularCoupling

/-! Plain Fp pads use two separately domain-separated 256-bit oracle answers.
Their concatenation is a uniform 512-bit integer. Reduction modulo p has a
small, explicitly bounded tail; it is never asserted to be exactly uniform. -/
namespace G1Release.Submission.DutyFreeFieldPad
open G1Release.Math

abbrev Label := SecretRelease.Label
abbrev Word := BN254.Fq
abbrev Raw := Label × Label

set_option exponentiation.threshold 1024

def rawEquiv : Raw ≃ Fin (2^512) :=
  (Equiv.prodComm _ _).trans
    ((Equiv.prodCongr (FiniteProbability.bytesFinEquiv 32)
      (FiniteProbability.bytesFinEquiv 32)).trans
      (finProdFinEquiv.trans (finCongr (by decide))))

def sample (raw : Raw) : Word :=
  ((FastRead.read (n := 4) raw.1 + 2^256 * FastRead.read (n := 4) raw.2 : Nat) : Word)

theorem label_value (label : Label) :
    (FiniteProbability.bytesFinEquiv 32 label).val = FastRead.read (n := 4) label := by
  rw [FastRead.read_eq]
  exact HintPadTransport.byteNatEquiv_val label

theorem raw_value (raw : Raw) :
    (rawEquiv raw).val = FastRead.read (n := 4) raw.1 + 2^256 * FastRead.read (n := 4) raw.2 := by
  change (FiniteProbability.bytesFinEquiv 32 raw.1).val +
    2^256 * (FiniteProbability.bytesFinEquiv 32 raw.2).val = _
  rw [label_value, label_value]

theorem sample_eq (raw : Raw) : sample raw = ((rawEquiv raw).val : Word) := by
  rw [raw_value]
  rfl

def transport (difference : Word) : Equiv.Perm Raw :=
  rawEquiv.trans
    ((DutyFreeModularCoupling.transport (2^512) baseFieldModulus
      (HintPadTransport.maskPermutation difference)).trans rawEquiv.symm)

def bad : Set Raw := rawEquiv ⁻¹' DutyFreeModularCoupling.bad (2^512) baseFieldModulus

theorem bad_card : Nat.card bad = (2^512)%baseFieldModulus := by
  unfold bad
  rw [Nat.card_congr (FiniteProbability.preimageEquiv rawEquiv _),
    DutyFreeModularCoupling.bad_card]

theorem transport_sample (difference : Word) (raw : Raw) (h : raw ∉ bad) :
    sample (transport difference raw) = sample raw + difference := by
  have hp : 0 < baseFieldModulus := by decide
  have he := DutyFreeModularCoupling.transports_residue (2^512) baseFieldModulus hp
    (HintPadTransport.maskPermutation difference) (rawEquiv raw) h
  rw [sample_eq, sample_eq]
  simp only [transport, Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [← ZMod.natCast_mod
    ((DutyFreeModularCoupling.transport (2^512) baseFieldModulus
      (HintPadTransport.maskPermutation difference) (rawEquiv raw)).val) baseFieldModulus, he]
  have hm := HintPadTransport.wordEquiv_maskPermutation difference
    (⟨(rawEquiv raw).val%baseFieldModulus, Nat.mod_lt _ hp⟩ : Fin baseFieldModulus)
  change (((HintPadTransport.maskPermutation difference)
      ⟨(rawEquiv raw).val%baseFieldModulus, Nat.mod_lt _ hp⟩).val : Word) =
    (((rawEquiv raw).val%baseFieldModulus : Nat) : Word) + difference at hm
  rw [ZMod.natCast_mod] at hm
  exact hm

end G1Release.Submission.DutyFreeFieldPad
