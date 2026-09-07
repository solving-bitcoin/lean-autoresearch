import Blake3Prize.Submission.RomMixedGuessing
import Blake3Prize.Submission.RomMixedConditional
import Blake3Prize.Submission.RomOracleLaw
import Blake3Prize.Submission.RomMeasurable

/-! A table-level ROM reduction. The hypotheses are concrete algebraic and
encoding facts: unique addresses, active rows determined by active labels,
and one hidden-label guess recoverable from any inactive-row query. No
security assertion is assumed by this interface. -/
namespace Blake3Prize.Submission.RomTableModel
open SecretRelease MeasureTheory ProbabilityTheory RomMixedKeys RomMixedGuessing

abbrev Address := List (Fin 256)

structure Model (e k : Nat) (Slot : Type) where
  externalBits : Fin e → Bool
  internalBits : Fin k → Bool
  isActive : Slot → Bool
  address : Keys e k → Slot → Address
  payload : Keys e k → Slot → Label
  publicAddress : Active e k → Slot → Address
  publicPayload : Active e k → Slot → Label
  address_injective : ∀ keys, Function.Injective (address keys)
  address_active : ∀ keys slot, isActive slot = true →
    address keys slot = publicAddress (split externalBits internalBits keys).1 slot
  payload_active : ∀ keys slot, isActive slot = true →
    payload keys slot = publicPayload (split externalBits internalBits keys).1 slot
  guess : Address → Option (Index e k × Label)
  guess_inactive : ∀ keys slot, isActive slot = false →
    ∃ i, guess (address keys slot) =
      some (i,key keys i (!(bit externalBits internalBits i)))

abbrev Inactive (model : Model e k Slot) := {s : Slot // model.isActive s = false}
abbrev Extended (model : Model e k Slot) := Address ⊕ Inactive model → Label

def selected (model : Model e k Slot) (keys : Keys e k) : Active e k :=
  ((fun i => (keys.1 i).get (model.externalBits i)),
    fun i => keys.2 i (model.internalBits i))

theorem selected_eq (model : Model e k Slot) (keys : Keys e k) :
    selected model keys = (split model.externalBits model.internalBits keys).1 := rfl

def ciphertexts (model : Model e k Slot) (keys : Keys e k) (oracle : ROM.Oracle) :
    Slot → Label := fun slot => RomBytes.xor (model.payload keys slot) (oracle (model.address keys slot))

noncomputable def programmed (model : Model e k Slot) (keys : Keys e k)
    (oracle : Extended model) : ROM.Oracle :=
  RomOracleLaw.program (fun s : Inactive model => model.address keys s.val)
    (fun s => model.payload keys s.val) oracle

def base (oracle : Extended model) : ROM.Oracle := fun q => oracle (.inl q)

def idealCiphertexts (model : Model e k Slot) (active : Active e k)
    (oracle : Extended model) : Slot → Label := fun slot =>
  if h : model.isActive slot = false then oracle (.inr ⟨slot,h⟩)
  else RomBytes.xor (model.publicPayload active slot) (oracle (.inl (model.publicAddress active slot)))

theorem ciphertexts_programmed (model : Model e k Slot) (keys : Keys e k)
    (oracle : Extended model) :
    ciphertexts model keys (programmed model keys oracle) =
      idealCiphertexts model (selected model keys) oracle := by
  funext slot
  by_cases h : model.isActive slot = false
  · rw [idealCiphertexts,dif_pos h]
    unfold ciphertexts programmed
    rw [RomOracleLaw.program_at _
      (fun a b hab => Subtype.ext (model.address_injective keys hab)) _ oracle ⟨slot,h⟩]
    exact RomBytes.xor_cancel_left _ _
  · rw [idealCiphertexts,dif_neg h]
    have ht : model.isActive slot = true := by cases hs : model.isActive slot <;> simp_all
    have hout : ¬∃ s : Inactive model, model.address keys s.val = model.address keys slot := by
      rintro ⟨s,hs⟩
      exact h ((congrArg model.isActive (model.address_injective keys hs)).symm.trans s.property)
    unfold ciphertexts programmed
    rw [RomOracleLaw.program_outside _ _ _ _ hout,
      model.address_active keys slot ht,model.payload_active keys slot ht]
    rfl

noncomputable def queryGuesses (model : Model e k Slot) (hash : Hash) (program : Program α) :
    List (Index e k × Label) :=
  (RomROMTrace.queries hash program).filterMap
    (fun query => model.guess (query.data.toList.map UInt8.toFin))

noncomputable def guesses (model : Model e k Slot) (hash : Hash)
    (program : Program (Index e k × Label)) : List (Index e k × Label) :=
  queryGuesses model hash program ++ [ROM.run hash program]

theorem guesses_length (model : Model e k Slot) (hash : Hash)
    (program : Program (Index e k × Label)) (q : Nat)
    (hb : OracleComp.IsTotalQueryBound program q) : (guesses model hash program).length ≤ q+1 := by
  have hq := (List.length_filterMap_le
    (fun query : ByteArray => model.guess (query.data.toList.map UInt8.toFin))
    (RomROMTrace.queries hash program)).trans (RomROMTrace.queries_length_le hash program q hb)
  simp only [guesses,List.length_append,List.length_singleton,queryGuesses]
  omega

theorem win_implies_guesses (model : Model e k Slot) (active : Active e k) (ranks : Ranks e k)
    (oracle : Extended model) (program : Program (Index e k × Label))
    (hw : let keys := (split model.externalBits model.internalBits).symm (active,ranks)
      let result := ROM.run (ROM.hash (programmed model keys oracle)) program
      key keys result.1 (!(bit model.externalBits model.internalBits result.1)) = result.2) :
    ranks ∈ guessesEvent active (guesses model (ROM.hash (base oracle)) program) := by
  classical
  let keys := (split model.externalBits model.internalBits).symm (active,ranks)
  by_cases hh : ∃ query ∈ RomROMTrace.queries (ROM.hash (base oracle)) program,
      ∃ slot : Inactive model, model.address keys slot.val = query.data.toList.map UInt8.toFin
  · obtain ⟨query,hquery,slot,hslot⟩ := hh
    obtain ⟨i,hi⟩ := model.guess_inactive keys slot.val slot.property
    refine ⟨(i,hidden active ranks i),?_,rfl⟩
    apply List.mem_append_left
    apply List.mem_filterMap.mpr
    refine ⟨query,hquery,?_⟩
    rw [← hslot,hi,inverse_hidden]
  · have heq : ROM.run (ROM.hash (base oracle)) program =
        ROM.run (ROM.hash (programmed model keys oracle)) program := by
      apply RomROMTrace.run_eq_of_agree
      intro query hquery
      symm
      exact RomOracleLaw.program_outside _ _ _ _ (fun hex => hh ⟨query,hquery,hex⟩)
    refine ⟨ROM.run (ROM.hash (base oracle)) program,
      List.mem_append_right _ (List.mem_singleton_self _),?_⟩
    change hidden active ranks (ROM.run (ROM.hash (base oracle)) program).1 = _
    rw [heq]
    exact (inverse_hidden _ _ active ranks _).symm.trans hw

end Blake3Prize.Submission.RomTableModel
