import G1Release.Submission.DutyFreeRealIdeal
import G1Release.Submission.ROMTrace

/-! Each oracle query can identify at most one hidden-label guess because
its public frame is injective. An execution that recovers an opposite label
either queried a hidden label first or guessed it as its final result. -/
namespace G1Release.Submission.DutyFreeQueryGuessing
open SecretRelease G1Release.Protected DutyFreeLayout DutyFreeSlots DutyFreeRealIdeal
open OracleComp
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev Index := Fin 512 ⊕ Fin 128
abbrev Guess := Index × Label

def index : Slot → Index
  | .inl slot => .inl (externalWire slot)
  | .inr slot => .inr (hotId slot)

def secrets (keys : Keys) (hot : HotKeys) (input : Input) : Index → Label
  | .inl wire => (keys wire).get (!(inputCodec.encode input)[wire.val])
  | .inr id => hot id (selectedCell input id)

theorem secret_index (keys : Keys) (hot : HotKeys) (input : Input) (slot : Slot) :
    secret keys hot input slot = secrets keys hot input (index slot) := by
  cases slot <;> rfl

def encoded (input : Input) (value : Slot × Label) : List (Fin 256) :=
  OracleAddress.query value.2 (purpose value.1) (row input value.1)

theorem encoded_injective (input : Input) : Function.Injective (encoded input) := by
  intro a b h
  have hh := OracleAddress.query_injective (purpose_lt a.1) (purpose_lt b.1)
    (row_lt input a.1) (row_lt input b.1) h
  exact Prod.ext (frame_injective input hh.2.1 hh.2.2) hh.1

noncomputable def listGuess (input : Input) (query : List (Fin 256)) : Option Guess := by
  letI : Decidable (∃ value, encoded input value = query) := Classical.propDecidable _
  exact if h : ∃ value, encoded input value = query then
    some (index (Classical.choose h).1, (Classical.choose h).2) else none

theorem listGuess_encoded (input : Input) (value : Slot × Label) :
    listGuess input (encoded input value) = some (index value.1,value.2) := by
  classical
  have he : ∃ v, encoded input v = encoded input value := ⟨value,rfl⟩
  have hc := encoded_injective input (Classical.choose_spec he)
  simp [listGuess, he, hc]

noncomputable def byteGuess (input : Input) (query : ByteArray) : Option Guess :=
  listGuess input (query.data.toList.map UInt8.toFin)

noncomputable def queryGuesses (input : Input) (hash : Hash) (program : Program α) : List Guess :=
  (ROMTrace.queries hash program).filterMap (byteGuess input)

theorem queryGuesses_length (input : Input) (hash : Hash) (program : Program α) (q : Nat)
    (hb : IsTotalQueryBound program q) : (queryGuesses input hash program).length ≤ q :=
  (List.length_filterMap_le _ _).trans (ROMTrace.queries_length_le hash program q hb)

noncomputable def guesses (input : Input) (hash : Hash) (program : Program (Fin 512 × Label)) :
    List Guess := queryGuesses input hash program ++ [(.inl (ROM.run hash program).1, (ROM.run hash program).2)]

theorem guesses_length (input : Input) (hash : Hash) (program : Program (Fin 512 × Label)) (q : Nat)
    (hb : IsTotalQueryBound program q) : (guesses input hash program).length ≤ q+1 := by
  have hq := queryGuesses_length input hash program q hb
  simp only [guesses, List.length_append, List.length_singleton]
  omega

def guessed (hidden : Index → Label) (values : List Guess) : Prop :=
  ∃ value ∈ values, hidden value.1 = value.2

theorem run_eq_without_hit (keys : Keys) (hot : HotKeys) (input : Input)
    (oracle : ExtendedOracle) (program : Program α)
    (hn : ¬∃ query ∈ ROMTrace.queries (ROM.hash (base oracle)) program,
      ∃ slot, address keys hot input slot = query.data.toList.map UInt8.toFin) :
    ROM.run (ROM.hash (base oracle)) program =
      ROM.run (ROM.hash (programmed keys hot input oracle)) program := by
  apply ROMTrace.run_eq_of_agree
  intro query hquery
  symm
  exact OracleLaw.program_outside _ _ _ _ (fun hex => hn ⟨query,hquery,hex⟩)

theorem hit_implies_guess (keys : Keys) (hot : HotKeys) (input : Input)
    (oracle : ExtendedOracle) (program : Program α)
    (hh : ∃ query ∈ ROMTrace.queries (ROM.hash (base oracle)) program,
      ∃ slot, address keys hot input slot = query.data.toList.map UInt8.toFin) :
    guessed (secrets keys hot input) (queryGuesses input (ROM.hash (base oracle)) program) := by
  obtain ⟨query,hquery,slot,hslot⟩ := hh
  let g : Guess := (index slot, secret keys hot input slot)
  have hd : byteGuess input query = some g := by
    unfold byteGuess
    rw [← hslot]
    exact listGuess_encoded input (slot,g.2)
  refine ⟨g, List.mem_filterMap.mpr ⟨query,hquery,hd⟩, ?_⟩
  exact (secret_index keys hot input slot).symm

theorem win_implies_guesses (keys : Keys) (hot : HotKeys) (input : Input)
    (oracle : ExtendedOracle) (program : Program (Fin 512 × Label)) (privateValue : Private)
    (hw : challenge.wins (ROM.hash (programmed keys hot input oracle)) privateValue input keys ()
      (ROM.run (ROM.hash (programmed keys hot input oracle)) program)) :
    guessed (secrets keys hot input) (guesses input (ROM.hash (base oracle)) program) := by
  classical
  by_cases hh : ∃ query ∈ ROMTrace.queries (ROM.hash (base oracle)) program,
      ∃ slot, address keys hot input slot = query.data.toList.map UInt8.toFin
  · obtain ⟨guess,hguess,he⟩ := hit_implies_guess keys hot input oracle program hh
    exact ⟨guess,List.mem_append_left _ hguess,he⟩
  · have heq := run_eq_without_hit keys hot input oracle program hh
    refine ⟨(.inl (ROM.run (ROM.hash (base oracle)) program).1,
      (ROM.run (ROM.hash (base oracle)) program).2), ?_, ?_⟩
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · change (ROM.run (ROM.hash (programmed keys hot input oracle)) program).2 =
        secrets keys hot input (.inl (ROM.run (ROM.hash (programmed keys hot input oracle)) program).1) at hw
      rw [← heq] at hw
      exact hw.symm

end G1Release.Submission.DutyFreeQueryGuessing
