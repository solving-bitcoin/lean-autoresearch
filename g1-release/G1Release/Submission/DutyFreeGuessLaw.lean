import G1Release.Submission.DutyFreeQueryGuessing
import G1Release.Submission.DutyFreeKeySplit
import G1Release.Submission.DutyFreePadLaw

/-! One common guessing bound for opposite Lamport labels and unreleased
bridge keys. Distinct-pair conditioning costs 2^256-1; independent bridge
keys have the larger denominator 2^256. Thus each query costs at most
1/(2^256-1), regardless of which kind of label its frame selects. -/
namespace G1Release.Submission.DutyFreeGuessLaw
open SecretRelease MeasureTheory ProbabilityTheory
open DutyFreeQueryGuessing LamportGuessing

abbrev State (active : Fin 512 → Label) := HiddenKeys active × DutyFreeKeySplit.Hidden

noncomputable def law (active : Fin 512 → Label) : Measure (State active) :=
  (hiddenLaw active).prod (uniformOn Set.univ)

instance (active : Fin 512 → Label) : IsProbabilityMeasure (hiddenLaw active) := by
  unfold hiddenLaw
  infer_instance

def labels (active : Fin 512 → Label) (state : State active) : Index → Label
  | .inl wire => (state.1 wire).val
  | .inr id => state.2 id

def event (active : Fin 512 → Label) (guess : Guess) : Set (State active) :=
  {state | labels active state guess.1 = guess.2}

theorem event_measurable (active : Fin 512 → Label) (guess : Guess) :
    MeasurableSet (event active guess) := MeasurableSet.of_discrete

theorem one_guess (active : Fin 512 → Label) (guess : Guess) :
    law active (event active guess) ≤ (1 : ENNReal) / (2^256-1 : Nat) := by
  rcases guess with ⟨wire | id,label⟩
  · have he : event active (.inl wire,label) = guessEvent active (wire,label) ×ˢ Set.univ := by
      ext state
      simp [event, labels, guessEvent]
    rw [he, law, Measure.prod_prod]
    simpa only [measure_univ, mul_one] using guess_probability_le active (wire,label)
  · have he : event active (.inr id,label) = Set.univ ×ˢ
        {hidden : DutyFreeKeySplit.Hidden | hidden id = label} := by
      ext state
      simp [event, labels]
    rw [he, law, Measure.prod_prod, measure_univ, one_mul]
    have hm := DutyFreePadLaw.eval_preserving (β := Label) id
    have heq : uniformOn (Set.univ : Set DutyFreeKeySplit.Hidden) {hidden | hidden id = label} =
        uniformOn (Set.univ : Set Label) {label} :=
      hm.measure_preimage (measurableSet_singleton label).nullMeasurableSet
    rw [heq]
    have hs : uniformOn (Set.univ : Set Label) {label} = 1 / (2^256 : Nat) := by
      classical
      letI := Fintype.ofFinite Label
      simp [uniformOn_univ, ← Nat.card_eq_fintype_card, FiniteProbability.label_card]
    rw [hs]
    apply ENNReal.div_le_div_left
    exact_mod_cast Nat.sub_le (2^256) 1

theorem guesses_bound (active : Fin 512 → Label) (guesses : List Guess) :
    law active {state | guessed (labels active state) guesses} ≤
      (guesses.length : ENNReal) / (2^256-1 : Nat) := by
  induction guesses with
  | nil => simp [guessed]
  | cons g gs ih =>
    have he : {state | guessed (labels active state) (g::gs)} =
        event active g ∪ {state | guessed (labels active state) gs} := by
      ext state
      simp [guessed, event]
    rw [he]
    apply (measure_union_le _ _).trans
    calc
      law active (event active g) + law active {state | guessed (labels active state) gs} ≤
          1 / (2^256-1 : Nat) + (gs.length : ENNReal) / (2^256-1 : Nat) :=
        add_le_add (one_guess active g) ih
      _ = _ := by
        rw [← ENNReal.add_div]
        congr 1
        simp [add_comm]

theorem rank_guesses_bound (active : Fin 512 → Label) (guesses : List Guess) :
    ((uniformOn (Set.univ : Set (Fin 512 → LamportLaw.Rank))).prod
      (uniformOn (Set.univ : Set DutyFreeKeySplit.Hidden)))
      {state | guessed (labels active (LamportLaw.hiddenFromRanks active state.1,state.2)) guesses} ≤
        (guesses.length : ENNReal) / (2^256-1 : Nat) := by
  have hm := (LamportLaw.hiddenFromRanks_preserving active).prod
    (MeasurePreserving.id (uniformOn (Set.univ : Set DutyFreeKeySplit.Hidden)))
  exact (hm.measure_preimage (MeasurableSet.of_discrete : MeasurableSet
    {state : State active | guessed (labels active state) guesses}).nullMeasurableSet).trans_le
    (guesses_bound active guesses)

end G1Release.Submission.DutyFreeGuessLaw
