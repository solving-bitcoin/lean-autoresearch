import G1Release.Submission.DutyFreeReleaseReduction
import G1Release.Submission.DutyFreeSamplerLaw

/-! Connect the actual finite byte tape to the probability experiments.
The bridge-key suffix is independent of the arithmetic sampler, and the
unit output-key component is discarded without changing the law. -/
namespace G1Release.Submission.DutyFreeSampleBridge
open SecretRelease G1Release.Protected DutyFreeGameLaw DutyFreeSamplerLaw
open MeasureTheory ProbabilityTheory
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

local instance : MeasurableSpace DutyFreeSlots.Keys := ⊤
local instance : MeasurableSpace challenge.inputs.Keys := ⊤
local instance : MeasurableSpace challenge.outputs.Keys := ⊤

noncomputable abbrev samplerLaw (hidden : Private) :=
  CosetSamplerMeasure.samplerLaw CosetSampler.coinBytes CosetSampler.sample hidden

def state (hidden : Private) (ω : ROM.Sample DutyFreeSampler.scheme) : RealState hidden :=
  ((ω.1,(fullSample ω.2.2.1 hidden).2),(fullSample ω.2.2.1 hidden).1,ω.2.2.2)

theorem preserving (hidden : Private) :
    MeasurePreserving (state hidden) (ROM.law DutyFreeSampler.scheme) (realLaw hidden (samplerLaw hidden)) := by
  let μk : Measure DutyFreeSlots.Keys := uniformOn Set.univ
  let μr := samplerLaw hidden
  let μh : Measure DutyFreeSlots.HotKeys := uniformOn Set.univ
  let μo := OracleLaw.law (List (Fin 256))
  have hd : MeasurePreserving
      (Prod.snd : challenge.outputs.Keys × Bytes DutyFreeSampler.coinBytes × ROM.Oracle → _)
      ((uniformOn (Set.univ : Set challenge.outputs.Keys)).prod
        ((uniformOn (Set.univ : Set (Bytes DutyFreeSampler.coinBytes))).prod μo))
      ((uniformOn (Set.univ : Set (Bytes DutyFreeSampler.coinBytes))).prod μo) := measurePreserving_snd
  have hs := (MeasurePreserving.id μk).prod
    (((DutyFreeSamplerLaw.preserving hidden).prod (MeasurePreserving.id μo)).comp hd)
  have ha := (measurePreserving_prodAssoc μk (μr.prod μh) μo).symm
    (MeasurableEquiv.prodAssoc : (DutyFreeSlots.Keys × FullRandomness hidden) × ROM.Oracle ≃ᵐ
      DutyFreeSlots.Keys × FullRandomness hidden × ROM.Oracle)
  have hb := (MeasurePreserving.id μk).prod (Measure.measurePreserving_swap (μ := μr) (ν := μh))
  have hc := (measurePreserving_prodAssoc μk μh μr).symm
    (MeasurableEquiv.prodAssoc : (DutyFreeSlots.Keys × DutyFreeSlots.HotKeys) × Randomness hidden ≃ᵐ
      DutyFreeSlots.Keys × DutyFreeSlots.HotKeys × Randomness hidden)
  have hm := measurePreserving_prodAssoc (μk.prod μh) μr μo
  have result := hm.comp (((hc.comp hb).prod (MeasurePreserving.id μo)).comp (ha.comp hs))
  have hu : μk.prod μh = uniformOn (Set.univ : Set KeyPair) := LamportLaw.prod_uniform_univ
  rw [hu] at result
  exact result

private theorem viewParts (scheme : SecretRelease.Scheme challenge)
    (hidden : Private) (input : Input) (ω : ROM.Sample scheme) :
    ROM.view scheme hidden input ω =
      DutyFreeGameViews.make hidden input (DutyFreeRealIdeal.active ω.1 input)
        (scheme.garbleBytes (ROM.hash ω.2.2.2) ω.2.2.1 hidden ω.1 ω.2.1) := rfl

private theorem encode_garble {c : Challenge} (scheme : SecretRelease.Scheme c)
    (hash : Hash) (coins : Bytes scheme.randomnessBytes) (hidden : c.Private)
    (keys : c.inputs.Keys) (outputs : c.outputs.Keys) (artifact : scheme.Artifact)
    (he : scheme.garble hash coins hidden keys outputs = artifact) :
    scheme.garbleBytes hash coins hidden keys outputs = scheme.encode artifact :=
  congrArg scheme.encode he

private theorem garbleBytesWith (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys)
    (hash : Hash) (coins : Bytes n) (hidden : Private)
    (keys : challenge.inputs.Keys) (outputs : challenge.outputs.Keys) :
    (DutyFreeSampler.schemeWith n sampler).garbleBytes hash coins hidden keys outputs =
      DutyFreeArtifact.encode (DutyFreeProgram.garble hash hidden
        (sampler coins hidden).1 keys (sampler coins hidden).2) := by
  exact (encode_garble (DutyFreeSampler.schemeWith n sampler) hash coins hidden keys outputs _
    (DutyFreeSampler.schemeWith_garble n sampler hash coins hidden keys outputs)).trans
    (DutyFreeSampler.schemeWith_encode n sampler _)

private theorem viewWith (n : Nat) (sampler : Bytes n → (hidden : Private) →
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys)
    (hidden : Private) (input : Input) (ω : ROM.Sample (DutyFreeSampler.schemeWith n sampler)) :
    ROM.view (DutyFreeSampler.schemeWith n sampler) hidden input ω =
      DutyFreeGameViews.make hidden input (DutyFreeRealIdeal.active ω.1 input)
        (DutyFreeArtifact.encode (DutyFreeProgram.garble (ROM.hash ω.2.2.2) hidden
          (sampler ω.2.2.1 hidden).1 ω.1 (sampler ω.2.2.1 hidden).2)) := by
  exact (viewParts (DutyFreeSampler.schemeWith n sampler) hidden input ω).trans
    (congrArg (DutyFreeGameViews.make hidden input (DutyFreeRealIdeal.active ω.1 input))
      (garbleBytesWith n sampler (ROM.hash ω.2.2.2) ω.2.2.1 hidden ω.1 ω.2.1))

theorem view_eq (hidden : Private) (input : Input) (ω : ROM.Sample DutyFreeSampler.scheme) :
    ROM.view DutyFreeSampler.scheme hidden input ω =
      DutyFreeGameViews.real (ROM.hash ω.2.2.2) hidden (fullSample ω.2.2.1 hidden).1 ω.1
        (fullSample ω.2.2.1 hidden).2 input := by
  have hp := congrArg (fun sampled : DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys =>
    DutyFreeGameViews.make hidden input (DutyFreeRealIdeal.active ω.1 input)
      (DutyFreeArtifact.encode (DutyFreeProgram.garble (ROM.hash ω.2.2.2) hidden
        sampled.1 ω.1 sampled.2))) (DutyFreeSamplerLaw.sample_projection ω.2.2.1 hidden)
  exact (viewWith DutyFreeSampler.coinBytes DutyFreeSampler.sample hidden input ω).trans hp

theorem outcome_eq (hidden : Private) (input : Input) (adversary : View challenge → Program α)
    (ω : ROM.Sample DutyFreeSampler.scheme) :
    ROM.run (ROM.hash ω.2.2.2) (adversary (ROM.view DutyFreeSampler.scheme hidden input ω)) =
      realOutcome hidden input adversary (state hidden ω) := by
  rw [view_eq]
  rfl

theorem winEvent_eq (hidden : Private) (input : Input)
    (adversary : View challenge → Program challenge.Claim) :
    ROM.winEvent DutyFreeSampler.scheme hidden input adversary =
      state hidden ⁻¹' realWin hidden input adversary := by
  delta ROM.winEvent
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage, realWin, outcome_eq]
  rfl

theorem distinguishEvent_eq (hidden : Private) (input : Input)
    (adversary : View challenge → Program Bool) :
    ROM.distinguishEvent DutyFreeSampler.scheme hidden input adversary =
      state hidden ⁻¹' realDistinguish hidden input adversary := by
  delta ROM.distinguishEvent
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_preimage, realDistinguish, outcome_eq]

theorem win_measurable (hidden : Private) (input : Input)
    (adversary : View challenge → Program challenge.Claim) :
    MeasurableSet (ROM.winEvent DutyFreeSampler.scheme hidden input adversary) := by
  rw [winEvent_eq]
  exact (preserving hidden).measurable (realWin_measurable hidden input adversary)

theorem distinguish_measurable (hidden : Private) (input : Input)
    (adversary : View challenge → Program Bool) :
    MeasurableSet (ROM.distinguishEvent DutyFreeSampler.scheme hidden input adversary) := by
  rw [distinguishEvent_eq]
  exact (preserving hidden).measurable (realDistinguish_measurable hidden input adversary)

theorem win_probability_eq (hidden : Private) (input : Input)
    (adversary : View challenge → Program challenge.Claim) :
    ROM.law DutyFreeSampler.scheme (ROM.winEvent DutyFreeSampler.scheme hidden input adversary) =
      realLaw hidden (samplerLaw hidden) (realWin hidden input adversary) := by
  rw [winEvent_eq]
  exact (preserving hidden).measure_preimage (realWin_measurable hidden input adversary).nullMeasurableSet

theorem distinguish_probability_eq (hidden : Private) (input : Input)
    (adversary : View challenge → Program Bool) :
    ROM.law DutyFreeSampler.scheme (ROM.distinguishEvent DutyFreeSampler.scheme hidden input adversary) =
      realLaw hidden (samplerLaw hidden) (realDistinguish hidden input adversary) := by
  rw [distinguishEvent_eq]
  exact (preserving hidden).measure_preimage
    (realDistinguish_measurable hidden input adversary).nullMeasurableSet

end G1Release.Submission.DutyFreeSampleBridge
