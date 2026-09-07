import G1Release.Submission.CosetGameHops
import G1Release.Submission.CosetIdealGameCoupling

set_option maxRecDepth 4096
set_option maxHeartbeats 300000

namespace G1Release.Submission.CosetFunctionReduction
open SecretRelease G1Release.Protected CosetSampler CosetRealIdeal CosetGameLaw CosetSamplerMeasure
open MeasureTheory ProbabilityTheory

local instance : MeasurableSpace Keys := ⊤

theorem realLaw_close (hidden : Hidden) :
    EventBounds.Le (realLaw hidden (samplerLaw coinBytes sample hidden))
      (realLaw hidden (idealLaw hidden)) (ENNReal.ofReal samplingError) ∧
    EventBounds.Le (realLaw hidden (idealLaw hidden))
      (realLaw hidden (samplerLaw coinBytes sample hidden)) (ENNReal.ofReal samplingError) := by
  constructor
  · exact EventBounds.prod_left
      (EventBounds.prod_right (sampleLaw_close hidden).1 (OracleLaw.law (List (Fin 256))))
      (uniformOn (Set.univ : Set Keys))
  · exact EventBounds.prod_left
      (EventBounds.prod_right (sampleLaw_close hidden).2 (OracleLaw.law (List (Fin 256))))
      (uniformOn (Set.univ : Set Keys))

theorem probability_le (source target : Hidden) (input : Input)
    (hequal : GLVOffsetFamily.mapAt source input = GLVOffsetFamily.mapAt target input)
    (href : reference source input = reference target input)
    (adversary : View challenge → Program Bool) (q : Nat) (ha : ROM.Bounded adversary q) :
    realLaw source (samplerLaw coinBytes sample source) (realDistinguish source input adversary) ≤
      realLaw target (samplerLaw coinBytes sample target) (realDistinguish target input adversary) +
        (2 * ((q : ENNReal) / (2^256-1 : Nat)) + 2 * ENNReal.ofReal samplingError) := by
  let error := ENNReal.ofReal samplingError
  let guess := (q : ENNReal) / (2^256-1 : Nat)
  calc
    _ ≤ realLaw source (idealLaw source) (realDistinguish source input adversary) + error :=
      (realLaw_close source).1 _ (realDistinguish_measurable source input adversary)
    _ ≤ (extendedLaw source (idealLaw source) (idealDistinguish source input adversary) + guess) + error :=
      add_le_add (CosetGameHops.real_le_ideal source input (idealLaw source) adversary q ha) le_rfl
    _ = (extendedLaw target (idealLaw target) (idealDistinguish target input adversary) + guess) + error := by
      rw [CosetIdealGameCoupling.probability_eq source target input hequal href adversary]
    _ ≤ ((realLaw target (idealLaw target) (realDistinguish target input adversary) + guess) + guess) + error :=
      add_le_add (add_le_add (CosetGameHops.ideal_le_real target input (idealLaw target) adversary q ha) le_rfl) le_rfl
    _ ≤ (((realLaw target (samplerLaw coinBytes sample target) (realDistinguish target input adversary) + error) + guess) + guess) + error :=
      add_le_add (add_le_add (add_le_add ((realLaw_close target).2 _
        (realDistinguish_measurable target input adversary)) le_rfl) le_rfl) le_rfl
    _ = _ := by dsimp only [error,guess]; rw [two_mul, two_mul]; ac_rfl

end G1Release.Submission.CosetFunctionReduction
