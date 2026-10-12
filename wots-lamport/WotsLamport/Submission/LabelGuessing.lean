import WotsLamport.Submission.CoinEncoding
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.Finiteness

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

abbrev DistinctPair (A : Type) := {p : A × A // p.1 ≠ p.2}

def distinctPairSigmaEquiv (A : Type) : DistinctPair A ≃ ((a : A) × {b : A // a ≠ b}) where
  toFun p := ⟨p.val.1, p.val.2, p.property⟩
  invFun p := ⟨(p.1, p.2.val), p.2.property⟩
  left_inv p := by rcases p with ⟨⟨a,b⟩,h⟩; rfl
  right_inv p := by rcases p with ⟨a,b,h⟩; rfl

theorem distinctPair_card (A : Type) [Fintype A] [DecidableEq A] :
    Fintype.card (DistinctPair A) = Fintype.card A * (Fintype.card A-1) := by
  rw [Fintype.card_congr (distinctPairSigmaEquiv A), Fintype.card_sigma]
  simp [Fintype.card_subtype_compl, Fintype.card_subtype_eq', nsmul_eq_mul]

def pairValue {A : Type} (p : DistinctPair A) (selected : Bool) : A :=
  if selected then p.val.2 else p.val.1

/-- Giving one component of a uniform distinct pair for free leaves at most
one successful pair per revealed value for any deterministic guess function.
This is a counting result, not an independence assumption about the artifact. -/
theorem pairGuess_card_le (A : Type) [Fintype A] [DecidableEq A]
    (selected : Bool) (guess : A → A) :
    Fintype.card {p : DistinctPair A // guess (pairValue p selected) = pairValue p (!selected)} ≤
      Fintype.card A := by
  apply Fintype.card_le_of_injective (fun p => pairValue p.val selected)
  intro p q he
  apply Subtype.ext
  apply Subtype.ext
  have hp := p.property
  have hq := q.property
  cases selected with
  | false =>
    change p.val.val.1 = q.val.val.1 at he
    change guess p.val.val.1 = p.val.val.2 at hp
    change guess q.val.val.1 = q.val.val.2 at hq
    exact Prod.ext he (hp.symm.trans ((congrArg guess he).trans hq))
  | true =>
    change p.val.val.2 = q.val.val.2 at he
    change guess p.val.val.2 = p.val.val.1 at hp
    change guess q.val.val.2 = q.val.val.1 at hq
    exact Prod.ext (hp.symm.trans ((congrArg guess he).trans hq)) he

theorem uniform_pairGuess_bound (A : Type) [Fintype A] [DecidableEq A]
    [MeasurableSpace (DistinctPair A)] [DiscreteMeasurableSpace (DistinctPair A)]
    (selected : Bool) (guess : A → A) :
    uniformOn (Set.univ : Set (DistinctPair A))
      {p | guess (pairValue p selected) = pairValue p (!selected)} ≤
        (Fintype.card A : ENNReal) / (Fintype.card A * (Fintype.card A-1) : Nat) := by
  rw [uniformOn_univ, Measure.count_apply MeasurableSet.of_discrete,
    Set.encard, ENat.card_eq_coe_fintype_card]
  change (Fintype.card {p : DistinctPair A //
    guess (pairValue p selected) = pairValue p (!selected)} : ENNReal) /
      (Fintype.card (DistinctPair A) : ENNReal) ≤ _
  rw [distinctPair_card]
  exact ENNReal.div_le_div_right (by exact_mod_cast pairGuess_card_le A selected guess) _

/-- Exact protected label-pair space: the labels are distinct, so the coarse
guessing allowance is 2/2^256, rather than silently treating them as two
independent labels. Applying this to a game additionally needs its joint
view-independence theorem. -/
theorem uniform_labelGuess_bound (selected : Bool) (guess : Label → Label) :
    uniformOn (Set.univ : Set Pair)
      {p | guess (p.get selected) = p.get (!selected)} ≤ (2 : ENNReal) / 2^256 := by
  classical
  letI := Fintype.ofFinite Label
  have h := uniform_pairGuess_bound Label selected guess
  change uniformOn (Set.univ : Set Pair)
      {p | guess (p.get selected) = p.get (!selected)} ≤ _ at h
  apply h.trans
  rw [bytes_card]
  norm_num <;>
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp <;> norm_num

end WotsLamport.Submission
