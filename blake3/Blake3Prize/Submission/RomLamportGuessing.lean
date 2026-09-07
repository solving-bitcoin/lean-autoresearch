import Blake3Prize.Submission.RomFiniteProbability

/-! Conditional entropy of distinct Lamport pairs. Once the selected label
is fixed, its opposite is uniform on the other 2^256 - 1 labels. -/
namespace Blake3Prize.Submission.RomLamportGuessing
open SecretRelease MeasureTheory ProbabilityTheory

abbrev Complement (active : Label) := {secret : Label // secret ≠ active}

instance (active : Label) : Nonempty (Complement active) := by
  obtain ⟨pair⟩ := (inferInstance : Nonempty Pair)
  by_cases h : pair.val.1 = active
  · exact ⟨⟨pair.val.2, by intro heq; exact pair.property (h.trans heq.symm)⟩⟩
  · exact ⟨⟨pair.val.1, h⟩⟩

theorem complement_card (active : Label) : Nat.card (Complement active) = 2^256-1 := by
  classical
  letI := Fintype.ofFinite Label
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  simp only [Fintype.card_unique, ← Nat.card_eq_fintype_card, RomFiniteProbability.label_card]

def selectedPairEquiv (bit : Bool) : Pair ≃ (Σ active : Label, Complement active) where
  toFun pair := ⟨pair.get bit, ⟨pair.get (!bit), by
    cases bit
    · exact pair.property.symm
    · exact pair.property⟩⟩
  invFun p := if bit then ⟨(p.2.val,p.1), p.2.property⟩
    else ⟨(p.1,p.2.val), p.2.property.symm⟩
  left_inv pair := by cases bit <;> rfl
  right_inv p := by cases bit <;> rfl

abbrev HiddenKeys {ι : Type*} (active : ι → Label) := (i : ι) → Complement (active i)

noncomputable def hiddenLaw {ι : Type*} (active : ι → Label) : Measure (HiddenKeys active) :=
  Measure.infinitePi (fun i => uniformOn (Set.univ : Set (Complement (active i))))

def guessEvent {ι : Type*} (active : ι → Label) (guess : ι × Label) : Set (HiddenKeys active) :=
  {secrets | (secrets guess.1).val = guess.2}

theorem guessEvent_measurable {ι : Type*} (active : ι → Label) (guess : ι × Label) :
    MeasurableSet (guessEvent active guess) := by
  exact (measurable_subtype_coe.comp (measurable_pi_apply guess.1)) (measurableSet_singleton guess.2)

theorem guess_probability_le {ι : Type*} (active : ι → Label) (guess : ι × Label) :
    hiddenLaw active (guessEvent active guess) ≤ 1 / (2^256 - 1 : Nat) := by
  classical
  letI := Fintype.ofFinite (Complement (active guess.1))
  have hm := (measurePreserving_eval_infinitePi
    (fun i => uniformOn (Set.univ : Set (Complement (active i)))) guess.1).map_eq
  have hevent : MeasurableSet {secret : Complement (active guess.1) | secret.val = guess.2} :=
    MeasurableSet.of_discrete
  have hprob : hiddenLaw active (guessEvent active guess) =
      uniformOn Set.univ {secret : Complement (active guess.1) | secret.val = guess.2} := by
    rw [← hm, Measure.map_apply (measurable_pi_apply guess.1) hevent]
    rfl
  rw [hprob]
  by_cases hne : guess.2 ≠ active guess.1
  · have hset : {secret : Complement (active guess.1) | secret.val = guess.2} =
        {⟨guess.2,hne⟩} := by ext secret; simp [Subtype.ext_iff]
    rw [hset, uniformOn_univ]
    simp [← Nat.card_eq_fintype_card, complement_card]
  · have hset : {secret : Complement (active guess.1) | secret.val = guess.2} = ∅ := by
      ext secret
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro heq
      exact secret.property (heq.trans (not_ne_iff.mp hne))
    simp [hset]

def guessesEvent {ι : Type*} (active : ι → Label) (guesses : List (ι × Label)) :
    Set (HiddenKeys active) := {secrets | ∃ guess ∈ guesses, secrets ∈ guessEvent active guess}

theorem guesses_probability_le {ι : Type*} (active : ι → Label) (guesses : List (ι × Label)) :
    hiddenLaw active (guessesEvent active guesses) ≤
      (guesses.length : ENNReal) / (2^256 - 1 : Nat) := by
  induction guesses with
  | nil => simp [guessesEvent]
  | cons g gs ih =>
    have hset : guessesEvent active (g::gs) = guessEvent active g ∪ guessesEvent active gs := by
      ext secrets
      simp [guessesEvent]
    rw [hset]
    calc
      hiddenLaw active (guessEvent active g ∪ guessesEvent active gs) ≤
          hiddenLaw active (guessEvent active g) + hiddenLaw active (guessesEvent active gs) :=
        measure_union_le _ _
      _ ≤ 1 / (2^256 - 1 : Nat) + (gs.length : ENNReal) / (2^256 - 1 : Nat) :=
        add_le_add (guess_probability_le active g) ih
      _ = ((g::gs).length : ENNReal) / (2^256 - 1 : Nat) := by
        rw [← ENNReal.add_div]
        congr 1
        simp [add_comm]

end Blake3Prize.Submission.RomLamportGuessing
