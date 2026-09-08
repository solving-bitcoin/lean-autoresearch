import G1Release.Submission.RealIdeal
import G1Release.Submission.ROMTrace
import G1Release.Submission.LamportGuessing

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace G1Release.Submission.QueryGuessing
open SecretRelease G1Release.Protected IdealView Randomized RealIdeal
open OracleComp MeasureTheory

def encoded (value : Slot × Label) : List (Fin 256) :=
  OracleAddress.query value.2 (SlotAddresses.purpose value.1) value.1.2.2.val

theorem encoded_injective : Function.Injective encoded := by
  intro a b h
  have hc := OracleAddress.query_injective (SlotAddresses.purpose_lt a.1)
    (SlotAddresses.purpose_lt b.1) (by omega : a.1.2.2.val < 65536)
      (by omega : b.1.2.2.val < 65536) h
  exact Prod.ext (SlotAddresses.slot_eq hc.2.1 (Fin.ext hc.2.2)) hc.1

/-- A proof-only parser: an honest-format query identifies one wire and one
label guess. Its definition does not depend on any secret labels. -/
noncomputable def listGuess (query : List (Fin 256)) : Option (Fin 512 × Label) := by
  letI : Decidable (∃ value, encoded value = query) := Classical.propDecidable _
  exact if h : ∃ value, encoded value = query then
    some (SlotAddresses.wire (Classical.choose h).1, (Classical.choose h).2) else none

theorem listGuess_encoded (value : Slot × Label) :
    listGuess (encoded value) = some (SlotAddresses.wire value.1,value.2) := by
  classical
  have he : ∃ v, encoded v = encoded value := ⟨value,rfl⟩
  have hc := encoded_injective (Classical.choose_spec he)
  simp [listGuess, he, hc]

noncomputable def byteGuess (query : ByteArray) : Option (Fin 512 × Label) :=
  listGuess (query.data.toList.map UInt8.toFin)

noncomputable def queryGuesses (hash : Hash) (program : Program α) : List (Fin 512 × Label) :=
  (ROMTrace.queries hash program).filterMap byteGuess

theorem queryGuesses_length (hash : Hash) (program : Program α) (q : Nat)
    (hb : IsTotalQueryBound program q) : (queryGuesses hash program).length ≤ q :=
  (List.length_filterMap_le _ _).trans (ROMTrace.queries_length_le hash program q hb)

noncomputable def guesses (hash : Hash) (program : Program (Fin 512 × Label)) :
    List (Fin 512 × Label) := queryGuesses hash program ++ [ROM.run hash program]

theorem guesses_length (hash : Hash) (program : Program (Fin 512 × Label)) (q : Nat)
    (hb : IsTotalQueryBound program q) : (guesses hash program).length ≤ q+1 := by
  have hq := queryGuesses_length hash program q hb
  simp only [guesses, List.length_append, List.length_singleton]
  omega

theorem pair_get_ne (pair : Pair) (b : Bool) : pair.get (!b) ≠ pair.get b := by
  cases b
  · exact pair.property.symm
  · exact pair.property

def oppositeKeys (keys : Fin 512 → Pair) (input : Input) :
    LamportGuessing.HiddenKeys (selected keys input) := fun i =>
  ⟨(keys i).get (!(inputBits input i)), pair_get_ne (keys i) (inputBits input i)⟩

theorem oppositeKeys_slot (keys : Fin 512 → Pair) (input : Input) (slot : Slot) :
    (oppositeKeys keys input (SlotAddresses.wire slot)).val =
      (keys (SlotAddresses.wire slot)).get (!(SlotAddresses.bit input slot)) := by
  dsimp only [oppositeKeys, SlotAddresses.wire, SlotAddresses.bit]
  rw [inputBits_tableWire]

theorem run_eq_without_hit (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle) (program : Program α)
    (hn : ¬∃ query ∈ ROMTrace.queries (ROM.hash (baseOracle oracle)) program,
      ∃ slot, SlotAddresses.inactive keys input slot = query.data.toList.map UInt8.toFin) :
    ROM.run (ROM.hash (baseOracle oracle)) program =
      ROM.run (ROM.hash (programmed hidden random keys input oracle)) program := by
  apply ROMTrace.run_eq_of_agree
  intro query hquery
  symm
  exact OracleLaw.program_outside _ _ _ _ (fun hex => hn ⟨query,hquery,hex⟩)

/-- A real-oracle recovery either is the base execution's final guess, or
the base execution already queried an opposite label. -/
theorem win_implies_guesses (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle)
    (program : Program (Fin 512 × Label))
    (hw : challenge.wins (ROM.hash (programmed hidden random keys input oracle)) hidden input keys ()
      (ROM.run (ROM.hash (programmed hidden random keys input oracle)) program)) :
    oppositeKeys keys input ∈ LamportGuessing.guessesEvent (selected keys input)
      (guesses (ROM.hash (baseOracle oracle)) program) := by
  classical
  by_cases hh : ∃ query ∈ ROMTrace.queries (ROM.hash (baseOracle oracle)) program,
      ∃ slot, SlotAddresses.inactive keys input slot = query.data.toList.map UInt8.toFin
  · obtain ⟨query,hquery,slot,hslot⟩ := hh
    let g : Fin 512 × Label :=
      (SlotAddresses.wire slot, (keys (SlotAddresses.wire slot)).get (!(SlotAddresses.bit input slot)))
    have hdecode : byteGuess query = some g := by
      unfold byteGuess
      rw [← hslot]
      change listGuess (encoded (slot,g.2)) = some g
      exact listGuess_encoded (slot,g.2)
    refine ⟨g, ?_, ?_⟩
    · apply List.mem_append_left
      exact List.mem_filterMap.mpr ⟨query,hquery,hdecode⟩
    · exact oppositeKeys_slot keys input slot
  · have heq := run_eq_without_hit hidden random keys input oracle program hh
    refine ⟨ROM.run (ROM.hash (baseOracle oracle)) program, ?_, ?_⟩
    · exact List.mem_append_right _ (List.mem_singleton_self _)
    · have hw' : (ROM.run (ROM.hash (programmed hidden random keys input oracle)) program).2 =
          (keys (ROM.run (ROM.hash (programmed hidden random keys input oracle)) program).1).get
            (!(inputBits input (ROM.run (ROM.hash (programmed hidden random keys input oracle)) program).1)) := hw
      rw [← heq] at hw'
      simp only [LamportGuessing.guessEvent, Set.mem_setOf_eq, oppositeKeys]
      exact hw'.symm

theorem fixed_program_guess_bound (active : Fin 512 → Label) (hash : Hash)
    (program : Program (Fin 512 × Label)) (q : Nat) (hb : IsTotalQueryBound program q) :
    LamportGuessing.hiddenLaw active
      (LamportGuessing.guessesEvent active (guesses hash program)) ≤
        (q+1 : ENNReal) / (2^256-1 : Nat) := by
  apply (LamportGuessing.guesses_probability_le active (guesses hash program)).trans
  apply ENNReal.div_le_div_right
  exact_mod_cast guesses_length hash program q hb

end G1Release.Submission.QueryGuessing
