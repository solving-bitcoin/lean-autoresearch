import G1Release.Submission.SlotAddresses
import G1Release.Submission.OracleLaw

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace G1Release.Submission.RealIdeal
open G1Release.Math SecretRelease G1Release.Protected
open Randomized IdealView

abbrev ExtendedOracle := List (Fin 256) ⊕ Slot → Label

def inputBits (input : Input) (i : Fin 512) : Bool := (inputCodec.encode input)[i.val]
def selected (keys : Fin 512 → Pair) (input : Input) (i : Fin 512) : Label :=
  (keys i).get (inputBits input i)

theorem inputBits_tableWire (input : Input) (kind : ProjectiveMap.TableKind) (row : Fin 254) :
    inputBits input (tableWire kind row) = bitsFor kind input row := by
  cases kind with
  | shared => exact Scheme.encodeInput_bit_x input row
  | xXY => exact Scheme.encodeInput_bit_x input row
  | yCubic => exact Scheme.encodeInput_bit_x input row
  | yQuadratic => exact Scheme.encodeInput_bit_x input row
  | yLinear => exact Scheme.encodeInput_bit_x input row
  | zSquare => exact Scheme.encodeInput_bit_x input row
  | zCross => exact Scheme.encodeInput_bit_x input row
  | zLinear => exact Scheme.encodeInput_bit_x input row
  | xYY => exact Scheme.encodeInput_bit_y input row
  | xCorrection => exact Scheme.encodeInput_bit_y input row
  | zCorrection => exact Scheme.encodeInput_bit_y input row

theorem pairsFor_tableWire (keys : Fin 512 → Pair) (kind : ProjectiveMap.TableKind)
    (row : Fin 254) (branch : Bool) :
    ProjectiveMap.pairsFor (Scheme.xPairs keys) (Scheme.yPairs keys) kind row branch =
      (keys (tableWire kind row)).get branch := by cases kind <;> rfl

def payload (hidden : Hidden) (random : Randomness hidden) (input : Input) (slot : Slot) : Label :=
  AffineTable.encodeWord (AffineTable.share
    ((mapHidden hidden random.offsets random.scales random.chains slot.1).params slot.2.1)
    (random.tableMasks slot.1 slot.2.1 slot.2.2) slot.2.2 (!(SlotAddresses.bit input slot)))

noncomputable def programmed (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle) : ROM.Oracle :=
  OracleLaw.program (SlotAddresses.inactive keys input) (payload hidden random input) oracle

def baseOracle (oracle : ExtendedOracle) : ROM.Oracle := fun query => oracle (.inl query)
def fakeCiphertexts (oracle : ExtendedOracle) : InactiveCiphertexts := fun slot => oracle (.inr slot)

theorem ciphertext_programmed (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle)
    (index : Fin 161) (kind : ProjectiveMap.TableKind) (row : Fin 254) (branch : Bool) :
    AffineTable.ciphertextAt (ROM.hash (programmed hidden random keys input oracle))
      (ProjectiveMap.purpose index.val kind)
      (ProjectiveMap.pairsFor (Scheme.xPairs keys) (Scheme.yPairs keys) kind)
      ((mapHidden hidden random.offsets random.scales random.chains index).params kind)
      (random.masks index kind) row branch =
    if branch = bitsFor kind input row then
      AffineTable.encrypt (AffineTable.share
        ((mapHidden hidden random.offsets random.scales random.chains index).params kind)
        (random.tableMasks index kind row) row branch)
        (AffineTable.pad (ROM.hash (baseOracle oracle))
          (selected keys input (tableWire kind row)) (ProjectiveMap.purpose index.val kind) row.val)
    else fakeCiphertexts oracle (index,kind,row) := by
  let slot : Slot := (index,kind,row)
  have hselected : selected keys input (tableWire kind row) =
      (keys (tableWire kind row)).get (bitsFor kind input row) := by
    unfold selected
    rw [inputBits_tableWire]
  unfold AffineTable.ciphertextAt
  rw [pairsFor_tableWire]
  by_cases h : branch = bitsFor kind input row
  · rw [if_pos h, h, hselected]
    apply congrArg (AffineTable.encrypt (AffineTable.share
      ((mapHidden hidden random.offsets random.scales random.chains index).params kind)
      (random.tableMasks index kind row) row (bitsFor kind input row)))
    change OracleLaw.program (SlotAddresses.inactive keys input) (payload hidden random input)
      oracle (SlotAddresses.active keys input slot) = oracle (.inl (SlotAddresses.active keys input slot))
    exact OracleLaw.program_outside _ _ _ _ (SlotAddresses.active_not_inactive keys input slot)
  · rw [if_neg h]
    have hb : branch = !(bitsFor kind input row) := by
      cases branch <;> cases hb' : bitsFor kind input row <;> simp_all
    rw [hb]
    change Bytes.xor (payload hidden random input slot)
      (OracleLaw.program (SlotAddresses.inactive keys input) (payload hidden random input)
        oracle (SlotAddresses.inactive keys input slot)) = oracle (.inr slot)
    rw [OracleLaw.program_at _ (SlotAddresses.inactive_injective keys input)]
    exact Bytes.xor_cancel_left _ _

theorem maps_programmed (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle) :
    Randomized.maps (ROM.hash (programmed hidden random keys input oracle)) hidden random keys =
      IdealView.maps (ROM.hash (baseOracle oracle)) input hidden random
        (selected keys input) (fakeCiphertexts oracle) := by
  funext index
  apply ProjectiveMap.Artifact.ext
  funext kind
  apply Vector.ext
  intro k hk
  simp only [Randomized.maps, ProjectiveMap.garble, IdealView.maps,
    AffineTable.garble, IdealView.table, Bytes.ofFn, Vector.getElem_ofFn]
  rw [ciphertext_programmed]

theorem garble_programmed (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle) :
    Scheme.encode (Randomized.garble (ROM.hash (programmed hidden random keys input oracle))
      hidden random keys) =
    IdealView.garble (ROM.hash (baseOracle oracle)) input hidden random
      (selected keys input) (fakeCiphertexts oracle) := by
  change Scheme.encodeFrom _ 161 _ = Scheme.encodeFrom _ 161 _
  rw [maps_programmed]

end G1Release.Submission.RealIdeal
