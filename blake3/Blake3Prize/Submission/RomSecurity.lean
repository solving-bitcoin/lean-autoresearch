import Blake3Prize.Submission.RomRendering
import Blake3Prize.Submission.RomSampleLaw

namespace Blake3Prize.Submission.RomSecurity
open SecretRelease Blake3Prize.Protected RomKeyMaterial RomMixedGuessing
open MeasureTheory OracleComp

local instance : Countable challenge.Input := by change Countable Input; infer_instance
local instance : MeasurableSpace challenge.inputs.Keys := ⊤
local instance : MeasurableSpace challenge.outputs.Keys := ⊤

def liftClaim (claim : Fin 768 × Label) : KeyIndex × Label := (.inl claim.1,claim.2)
def liftAdversary (adversary : View challenge → Program (Fin 768 × Label)) :
    View challenge → Program (KeyIndex × Label) := fun view => liftClaim <$> adversary view

theorem lift_bounded (adversary : View challenge → Program (Fin 768 × Label)) (q : Nat)
    (ha : ROM.Bounded adversary q) : ROM.Bounded (liftAdversary adversary) q := by
  intro view
  exact (isQueryBound_map_iff (adversary view) liftClaim q _ _).mpr (ha view)

theorem run_map (hash : Hash) (program : Program α) (f : α → β) :
    ROM.run hash (f <$> program) = f (ROM.run hash program) := by
  change Id.run (simulateQ (QueryImpl.ofFn hash) (f <$> program)) =
    f (Id.run (simulateQ (QueryImpl.ofFn hash) program))
  rw [simulateQ_map]
  rfl

theorem wins_iff (hash : Hash) (p : Unit) (input : Input) (coins : Bytes 3915904)
    (inputs : Fin 512 → Pair) (outputs : Fin 256 → Pair) (claim : Fin 768 × Label) :
    challenge.wins hash p input inputs outputs claim ↔
      key (assemble coins inputs outputs) (.inl claim.1)
        (!(keyBit input (.inl claim.1))) = claim.2 := by
  change (claim.2 = if h : claim.1.val < 512 then
    (inputs ⟨claim.1.val,h⟩).get (!(inputBit input ⟨claim.1.val,h⟩)) else
    (outputs ⟨claim.1.val-512,by omega⟩).get
      (!((Codec.byteVector 32).encode (reference input)).get (⟨claim.1.val-512,by omega⟩ : Fin 256))) ↔ _
  change _ ↔ ((externalEquiv (inputs,outputs)) claim.1).get (!(externalBits input claim.1)) = claim.2
  by_cases h : claim.1.val < 512
  · simp only [dif_pos h,externalEquiv,Equiv.coe_fn_mk,externalBits,dif_pos h,eq_comm]
  · simp only [dif_neg h,externalEquiv,Equiv.coe_fn_mk,externalBits,dif_neg h,eq_comm]

theorem outcome_lift (input : Input) (p : Unit)
    (adversary : View challenge → Program (Fin 768 × Label)) (sample : ROM.Sample RomScheme.scheme) :
    RomTableSecurity.outcome (RomModelData.model input) (RomRendering.view input)
      (liftAdversary adversary) (RomSampleLaw.state sample) =
        liftClaim (ROM.run (ROM.hash sample.2.2.2) (adversary (ROM.view RomScheme.scheme p input sample))) := by
  unfold RomTableSecurity.outcome liftAdversary
  rw [run_map,RomRendering.actual_view input p sample]
  rfl

theorem event_eq (input : Input) (p : Unit)
    (adversary : View challenge → Program (Fin 768 × Label)) :
    ROM.winEvent RomScheme.scheme p input adversary =
      RomSampleLaw.state ⁻¹' RomTableSecurity.event (RomModelData.model input)
        (RomRendering.view input) (liftAdversary adversary) := by
  ext sample
  change challenge.wins (ROM.hash sample.2.2.2) p input sample.1 sample.2.1
    (ROM.run (ROM.hash sample.2.2.2) (adversary (ROM.view RomScheme.scheme p input sample))) ↔
    key (RomSampleLaw.state sample).1
      (RomTableSecurity.outcome _ _ _ (RomSampleLaw.state sample)).1
      (!(RomMixedGuessing.bit _ _ (RomTableSecurity.outcome _ _ _ (RomSampleLaw.state sample)).1)) =
      (RomTableSecurity.outcome _ _ _ (RomSampleLaw.state sample)).2
  rw [outcome_lift input p adversary sample]
  exact wins_iff (ROM.hash sample.2.2.2) p input sample.2.2.1 sample.1 sample.2.1
    (ROM.run (ROM.hash sample.2.2.2) (adversary (ROM.view RomScheme.scheme p input sample)))

theorem profile_bound (q : Nat) :
    (q+1 : ENNReal) / (2^256-1 : Nat) ≤ (challenge.rom.error q : ENNReal) := by
  have he : challenge.rom.error q = (q+1 : ℚ≥0) / 2^128 := rfl
  rw [he, ← ENNReal.coe_nnratCast]
  push_cast
  apply ENNReal.div_le_div_left
  norm_num

theorem release_secure : ROM.ReleaseSecure RomScheme.scheme := by
  intro p input q _ adversary ha
  have hm := RomSampleLaw.preserving
  have he := RomTableSecurity.event_measurable (RomModelData.model input)
    (RomRendering.view input) (liftAdversary adversary)
  rw [event_eq input p adversary]
  refine ⟨hm.measurable he,?_⟩
  rw [hm.measure_preimage he.nullMeasurableSet]
  exact (RomTableSecurity.probability_le (RomModelData.model input) (RomRendering.view input)
    (liftAdversary adversary) q (lift_bounded adversary q ha)).trans (profile_bound q)

def certificate : SecretRelease.Certificate RomScheme.scheme 7848000 where
  correct := RomScheme.correct
  decode_encode := RomBytes.decode_encode
  encode_decode := fun _ _ h => RomBytes.encode_decode h
  artifactBound := RomScheme.artifact_bound
  releaseSecure := release_secure
  withholdingSecure := True.intro
  functionPrivate := by intro leakage h; cases h

def candidate : Blake3Prize.Protected.Candidate :=
  ⟨RomScheme.scheme,7848000,some certificate⟩

end Blake3Prize.Submission.RomSecurity
