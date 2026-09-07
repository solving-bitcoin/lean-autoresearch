import G1Release.Submission.CosetIdealView
import G1Release.Submission.OracleLaw

namespace G1Release.Submission.CosetRealIdeal
open SecretRelease GarblingPrize.Protected G1Release.Protected
open CosetSlots CosetSampler
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev ExtendedOracle := List (Fin 256) ⊕ Slot → Label

def payload (_hidden : Hidden) (_random : Randomness _hidden) (_input : Input) (_slot : Slot) : Label :=
  Bytes.zero 32

noncomputable def programmed (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle) : ROM.Oracle :=
  OracleLaw.program (inactive keys input) (payload hidden random input) oracle

def baseOracle (oracle : ExtendedOracle) : ROM.Oracle := fun query => oracle (.inl query)
def fakePads (oracle : ExtendedOracle) : CosetIdealView.InactivePads := fun slot => oracle (.inr slot)

theorem pairsFor_tableWire (hash : Hash) (keys : Fin 512 → Pair) (kind : Fin 8)
    (row : Fin 254) (branch : Bool) (p : Nat) :
    CosetHintMap.inputFor kind (CosetScheme.xPads hash keys) (CosetScheme.yPads hash keys) row branch p =
      AffineTable.pad hash ((keys (tableWire kind row)).get branch) p row.val := by
  unfold CosetHintMap.inputFor tableWire
  split <;> rfl

theorem pad_programmed (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle)
    (slot : Slot) (branch : Bool) :
    AffineTable.pad (ROM.hash (programmed hidden random keys input oracle))
        ((keys (wire slot)).get branch) (purpose slot) slot.2.2.val =
      if branch = bit input slot then
        AffineTable.pad (ROM.hash (baseOracle oracle))
          (selected keys input (wire slot)) (purpose slot) slot.2.2.val
      else fakePads oracle slot := by
  have hs : selected keys input (wire slot) = (keys (wire slot)).get (bit input slot) := by
    unfold selected wire bit
    rw [inputBits_tableWire]
  by_cases h : branch = bit input slot
  · rw [if_pos h, h, hs]
    exact OracleLaw.program_outside _ _ _ _ (active_not_inactive keys input slot)
  · rw [if_neg h]
    have hb : branch = !(bit input slot) := by
      cases branch <;> cases hbit : bit input slot <;> simp_all
    rw [hb]
    change OracleLaw.program (inactive keys input) (payload hidden random input)
      oracle (inactive keys input slot) = oracle (.inr slot)
    rw [OracleLaw.program_at _ (inactive_injective keys input)]
    exact Bytes.zero_xor _

theorem rowState_programmed (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle)
    (index : Fin 91) (kind : Fin 8) (row : Fin 254) :
    ((CosetHintMap.inputFor kind
      (CosetScheme.xPads (ROM.hash (programmed hidden random keys input oracle)) keys)
      (CosetScheme.yPads (ROM.hash (programmed hidden random keys input oracle)) keys)
      row false (CosetHintMap.purpose index.val kind), random.2 index kind row),
      CosetHintMap.inputFor kind
      (CosetScheme.xPads (ROM.hash (programmed hidden random keys input oracle)) keys)
      (CosetScheme.yPads (ROM.hash (programmed hidden random keys input oracle)) keys)
      row true (CosetHintMap.purpose index.val kind)) =
      CosetIdealView.rowState (ROM.hash (baseOracle oracle)) input random
        (selected keys input) (fakePads oracle) (index,kind,row) := by
  rw [pairsFor_tableWire, pairsFor_tableWire]
  have hfalse := pad_programmed hidden random keys input oracle (index,kind,row) false
  have htrue := pad_programmed hidden random keys input oracle (index,kind,row) true
  dsimp only [wire, purpose] at hfalse htrue
  change ((_,random.2 index kind row),_) = _
  rw [hfalse, htrue]
  unfold CosetIdealView.rowState CosetRowCoupling.assemble
  cases bit input (index,kind,row) <;> rfl

theorem maps_programmed (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle) :
    (CosetScheme.garble (ROM.hash (programmed hidden random keys input oracle))
      hidden random.1 random.2 keys).maps =
      CosetIdealView.maps (ROM.hash (baseOracle oracle)) input hidden random
        (selected keys input) (fakePads oracle) := by
  funext index
  apply CosetHintMap.Artifact.ext
  funext kind
  change HintAffineTable.garble _ _ _ _ = _
  rw [HintAffineTablePrivacy.garble_eq_tableFromState]
  apply congrArg (HintAffineTablePrivacy.tableFromState _)
  funext row
  exact rowState_programmed hidden random keys input oracle index kind row

theorem garble_programmed (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle) :
    CosetScheme.encode (CosetScheme.garble (ROM.hash (programmed hidden random keys input oracle))
      hidden random.1 random.2 keys) =
      CosetIdealView.garble (ROM.hash (baseOracle oracle)) input hidden random
        (selected keys input) (fakePads oracle) := by
  apply congrArg CosetScheme.encode
  apply CosetFamilyArtifact.Artifact.ext
  exact maps_programmed hidden random keys input oracle

end G1Release.Submission.CosetRealIdeal
