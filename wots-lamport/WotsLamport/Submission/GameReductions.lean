import WotsLamport.Submission.GamePrograms

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory

def fixedMessageAdversary (m : Message) (a : View challenge → Program challenge.Claim) :
    AdaptiveAdversary where
  State := Unit
  choose := fun _ => pure (m, ())
  finish := fun _ => a

theorem fixedMessage_event (s : Scheme challenge) (m : Message)
    (a : View challenge → Program challenge.Claim) :
    adaptiveEvent s (fixedMessageAdversary m a) = ROM.winEvent s () m a := by
  ext ω
  rfl

/-- The separate adaptive theorem would imply the static post-release
certificate field, with exactly the same query budget and numerical target.
No adaptive theorem for this candidate is assumed or issued here. -/
theorem adaptive_implies_release (s : Scheme challenge) (secure : AdaptiveSecure s) :
    ROM.ReleaseSecure s := by
  intro p m q hq a bound
  cases p
  have chooseBound : ROM.Bounded (fixedMessageAdversary m a).choose 0 := by
    intro artifact
    trivial
  have finishBound : ∀ state, ROM.Bounded ((fixedMessageAdversary m a).finish state) q :=
    fun _ => bound
  have h := secure (fixedMessageAdversary m a) 0 q (by simpa using hq) chooseBound finishBound
  rw [fixedMessage_event s m a] at h
  simpa only [Nat.zero_add] using h

end WotsLamport.Submission
