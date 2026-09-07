import Blake3Prize.Submission.RomMixedKeys

namespace Blake3Prize.Submission.RomMixedGuessing
open SecretRelease MeasureTheory ProbabilityTheory RomMixedKeys RomLamportLaw

abbrev Index (e k : Nat) := Fin e ⊕ Fin k
instance (e k : Nat) : MeasurableSpace (Index e k) := ⊤

def key (keys : Keys e k) : Index e k → Bool → Label :=
  Sum.elim (fun i => (keys.1 i).get) keys.2

def activeLabel (active : Active e k) : Index e k → Label := Sum.elim active.1 active.2
def bit (external : Fin e → Bool) (internal : Fin k → Bool) : Index e k → Bool :=
  Sum.elim external internal

noncomputable def hidden (active : Active e k) (ranks : Ranks e k) : Index e k → Label :=
  Sum.elim (fun i => ((complementEquiv (active.1 i)).symm (ranks.1 i)).val) ranks.2

theorem inverse_active (external : Fin e → Bool) (internal : Fin k → Bool)
    (active : Active e k) (ranks : Ranks e k) (i : Index e k) :
    key ((split external internal).symm (active,ranks)) i (bit external internal i) =
      activeLabel active i := by
  cases i with
  | inl i =>
    change ((pairEquiv (external i)).symm (active.1 i,ranks.1 i)).get (external i) = _
    cases external i <;> rfl
  | inr i =>
    change (rawPairEquiv (internal i)).symm (active.2 i,ranks.2 i) (internal i) = _
    cases internal i <;> rfl

theorem inverse_hidden (external : Fin e → Bool) (internal : Fin k → Bool)
    (active : Active e k) (ranks : Ranks e k) (i : Index e k) :
    key ((split external internal).symm (active,ranks)) i (!(bit external internal i)) =
      hidden active ranks i := by
  cases i with
  | inl i =>
    change ((pairEquiv (external i)).symm (active.1 i,ranks.1 i)).get (!(external i)) = _
    cases external i <;> rfl
  | inr i =>
    change (rawPairEquiv (internal i)).symm (active.2 i,ranks.2 i) (!(internal i)) = _
    cases internal i <;> rfl

def guessEvent (active : Active e k) (guess : Index e k × Label) : Set (Ranks e k) :=
  {ranks | hidden active ranks guess.1 = guess.2}

theorem raw_guess_probability (i : Fin k) (label : Label) :
    uniformOn (Set.univ : Set (Fin k → Label)) {keys | keys i = label} =
      1 / (2^256 : Nat) := by
  classical
  letI := Fintype.ofFinite Label
  have hpi : Measure.infinitePi (fun _ : Fin k => uniformOn (Set.univ : Set Label)) =
      uniformOn (Set.univ : Set (Fin k → Label)) := by
    rw [Measure.infinitePi_eq_pi, ← uniformOn_pi (f := fun _ : Fin k => (Set.univ : Set Label))]
    simp
  have hm := measurePreserving_eval_infinitePi
    (fun _ : Fin k => uniformOn (Set.univ : Set Label)) i
  change uniformOn (Set.univ : Set (Fin k → Label)) (Function.eval i ⁻¹' {label}) = _
  rw [← hpi, hm.measure_preimage (measurableSet_singleton label).nullMeasurableSet]
  simp [uniformOn_univ, ← Nat.card_eq_fintype_card, RomFiniteProbability.label_card]

theorem guess_probability_le (active : Active e k) (guess : Index e k × Label) :
    uniformOn (Set.univ : Set (Ranks e k)) (guessEvent active guess) ≤
      1 / (2^256-1 : Nat) := by
  rw [← prod_uniform_univ]
  rcases guess with ⟨i,label⟩
  cases i with
  | inl i =>
    have he : guessEvent active (Sum.inl i,label) =
        {ranks : Fin e → Rank | ((complementEquiv (active.1 i)).symm (ranks i)).val = label}
          ×ˢ (Set.univ : Set (Fin k → Label)) := by ext ranks; simp [guessEvent,hidden]
    rw [he,Measure.prod_prod]
    simp only [measure_univ,mul_one]
    have hm := hiddenFromRanks_preserving active.1
    have hs := RomLamportGuessing.guessEvent_measurable active.1 (i,label)
    rw [show {ranks : Fin e → Rank |
        ((complementEquiv (active.1 i)).symm (ranks i)).val = label} =
      hiddenFromRanks active.1 ⁻¹' RomLamportGuessing.guessEvent active.1 (i,label) from rfl,
      hm.measure_preimage hs.nullMeasurableSet]
    exact RomLamportGuessing.guess_probability_le active.1 (i,label)
  | inr i =>
    have he : guessEvent active (Sum.inr i,label) =
        (Set.univ : Set (Fin e → Rank)) ×ˢ {keys : Fin k → Label | keys i = label} := by
      ext ranks; simp [guessEvent,hidden]
    rw [he,Measure.prod_prod]
    simp only [measure_univ,one_mul,raw_guess_probability]
    apply ENNReal.div_le_div_left
    exact_mod_cast (by omega : 2^256-1 ≤ 2^256)

def guessesEvent (active : Active e k) (guesses : List (Index e k × Label)) :
    Set (Ranks e k) := {ranks | ∃ guess ∈ guesses, ranks ∈ guessEvent active guess}

theorem guesses_probability_le (active : Active e k) (guesses : List (Index e k × Label)) :
    uniformOn (Set.univ : Set (Ranks e k)) (guessesEvent active guesses) ≤
      (guesses.length : ENNReal) / (2^256-1 : Nat) := by
  induction guesses with
  | nil => simp [guessesEvent]
  | cons g gs ih =>
    have he : guessesEvent active (g::gs) = guessEvent active g ∪ guessesEvent active gs := by
      ext ranks; simp [guessesEvent]
    rw [he]
    apply (measure_union_le _ _).trans
    apply (add_le_add (guess_probability_le active g) ih).trans_eq
    rw [← ENNReal.add_div]
    congr 1
    simp [add_comm]

end Blake3Prize.Submission.RomMixedGuessing
