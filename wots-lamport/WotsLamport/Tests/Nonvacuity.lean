import WotsLamport.Protected.Adaptive

/-! Author-owned regression theorem statements. These sources remain unchecked
until the pinned Lean compiler runs. No candidate certificate imports them. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 500000

namespace WotsLamport.Tests
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory

theorem opposite_claim_wins (h : Hash) (m : Message) (keys : Keys)
    (labels : challenge.outputs.Keys) (i : Fin 256) :
    challenge.wins h () m keys labels
      (i, (labels i).get (!(outputCodec.encode m)[i.val])) := by
  simp only [challenge]

theorem selected_claim_does_not_win (h : Hash) (m : Message) (keys : Keys)
    (labels : challenge.outputs.Keys) (i : Fin 256) :
    ¬ challenge.wins h () m keys labels
      (i, (labels i).get ((outputCodec.encode m)[i.val])) := by
  cases hb : (outputCodec.encode m)[i.val]
  · simpa [challenge, Pair.get, hb] using (labels i).property
  · simpa [challenge, Pair.get, hb] using Ne.symm (labels i).property

theorem withholding_checks_both_labels (h : Hash) (m : Message) (keys : Keys)
    (labels : challenge.outputs.Keys) (i : Fin 256) (b : Bool) :
    ∀ wins, challenge.withholding = some wins → wins h () m keys labels (i, (labels i).get b) := by
  intro wins he
  cases Option.some.inj he
  cases b <;> simp [Pair.get]

theorem law_univ (s : Scheme challenge) : ROM.law s Set.univ = 1 := by
  letI : MeasurableSpace challenge.inputs.Keys := ⊤
  letI : MeasurableSpace challenge.outputs.Keys := ⊤
  unfold ROM.law
  exact measure_univ

def zeroQueryAdversary (m : Message) (guess : challenge.Claim) : AdaptiveAdversary where
  State := Unit
  choose := fun _ => pure (m, ())
  finish := fun _ _ => pure guess

theorem zeroQueryAdversary_bounded (m : Message) (guess : challenge.Claim) :
    ROM.Bounded (zeroQueryAdversary m guess).choose 0 ∧
      ∀ state, ROM.Bounded ((zeroQueryAdversary m guess).finish state) 0 := by
  constructor
  · intro v; trivial
  · intro state v; trivial

/-- An adaptive zero-query attacker which always wins rules out the stronger
property. The law is a probability measure and the bound is strictly below one. -/
theorem adaptive_rejects_certain_recovery (s : Scheme challenge) (a : AdaptiveAdversary)
    (chooseBound : ROM.Bounded a.choose 0)
    (finishBound : ∀ state, ROM.Bounded (a.finish state) 0)
    (alwaysWins : ∀ ω, ω ∈ adaptiveEvent s a) : ¬ AdaptiveSecure s := by
  intro secure
  have bound := (secure a 0 0 (by decide) chooseBound finishBound).2
  have event : adaptiveEvent s a = Set.univ := Set.eq_univ_of_forall alwaysWins
  rw [event, law_univ] at bound
  have small : (challenge.rom.error 0 : ENNReal) < 1 := by
    rw [← ENNReal.coe_nnratCast, ENNReal.coe_lt_one_iff]
    exact_mod_cast challenge.rom.nontrivial 0 (Nat.zero_le _)
  exact (not_le_of_gt small) bound

end WotsLamport.Tests
