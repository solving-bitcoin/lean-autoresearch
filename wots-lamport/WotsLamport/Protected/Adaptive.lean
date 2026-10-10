import WotsLamport.Protected.Target

namespace WotsLamport.Protected
open SecretRelease

/-- Separate stronger experiment. The first stage sees the complete artifact,
including pk, then chooses a message; the second gets exactly one release and
the selected output labels. This is NOT implied by the static Certificate. -/
structure AdaptiveAdversary where
  State : Type
  choose : ByteArray → Program (Message × State)
  finish : State → View challenge → Program challenge.Claim

def adaptiveEvent (s : Scheme challenge) (a : AdaptiveAdversary) : Set (ROM.Sample s) :=
  {ω | let h := ROM.hash ω.2.2.2
       let artifact := s.garbleBytes h ω.2.2.1 () ω.1 ω.2.1
       let selected := ROM.run h (a.choose artifact)
       let view := ROM.view s () selected.1 ω
       challenge.wins h () selected.1 ω.1 ω.2.1
         (ROM.run h (a.finish selected.2 view))}

def AdaptiveSecure (s : Scheme challenge) : Prop :=
  letI : MeasurableSpace challenge.inputs.Keys := ⊤
  letI : MeasurableSpace challenge.outputs.Keys := ⊤
  ∀ (a : AdaptiveAdversary) q₁ q₂, q₁ + q₂ ≤ challenge.rom.maxQueries →
    ROM.Bounded a.choose q₁ →
    (∀ state, ROM.Bounded (a.finish state) q₂) →
    MeasurableSet (adaptiveEvent s a) ∧
    ROM.law s (adaptiveEvent s a) ≤ (challenge.rom.error (q₁ + q₂) : ENNReal)

end WotsLamport.Protected
