import WotsLamport.Submission.Shamir
import Mathlib.Probability.UniformOn
import Mathlib.Data.Set.Card

namespace WotsLamport.Submission.Shamir
open Polynomial MeasureTheory ProbabilityTheory

/-- Uniform probabilities are unchanged by a bijection of finite discrete
sample spaces. This is distribution transport, not a sampler assumption. -/
theorem uniform_event_equiv {A B : Type} [Finite A] [Finite B]
    [MeasurableSpace A] [MeasurableSpace B]
    [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B]
    (e : A ≃ B) (event : Set B) :
    uniformOn (Set.univ : Set A) (e ⁻¹' event) = uniformOn (Set.univ : Set B) event := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite B
  rw [uniformOn_univ, uniformOn_univ,
    Measure.count_apply MeasurableSet.of_discrete,
    Measure.count_apply MeasurableSet.of_discrete,
    Set.encard_preimage_of_bijective e.bijective, Fintype.card_congr e]

variable {F : Type} [Field F] [DecidableEq F]

def SecretPolynomials (t : Nat) (secret : F) :=
  {p : F[X] // p.degree < t ∧ p.eval 0 = secret}

instance [Finite F] (t : Nat) (secret : F) : Finite (SecretPolynomials t secret) := by
  apply Finite.of_injective (fun p : SecretPolynomials t secret =>
    fun i : Fin t => p.val.coeff i.val)
  intro p q he
  apply Subtype.ext
  apply Polynomial.ext
  intro n
  by_cases hn : n < t
  · exact congrFun he ⟨n, hn⟩
  · have hge : t ≤ n := Nat.le_of_not_gt hn
    rw [(Polynomial.degree_lt_iff_coeff_zero _ _).mp p.property.1 n hge,
      (Polynomial.degree_lt_iff_coeff_zero _ _).mp q.property.1 n hge]

instance (t : Nat) (secret : F) : MeasurableSpace (SecretPolynomials t secret) := ⊤

noncomputable def secretEquiv (s : Finset F) (nonzero : (0 : F) ∉ s)
    (t : Nat) (few : s.card < t) (a b : F) :
    SecretPolynomials t a ≃ SecretPolynomials t b where
  toFun p := ⟨shift s (b-a) p.val,
    shift_degree s nonzero t few (b-a) p.val p.property.1,
    by rw [shift_secret, p.property.2]; ring⟩
  invFun p := ⟨shift s (a-b) p.val,
    shift_degree s nonzero t few (a-b) p.val p.property.1,
    by rw [shift_secret, p.property.2]; ring⟩
  left_inv p := by
    apply Subtype.ext
    change shift s (a-b) (shift s (b-a) p.val) = p.val
    simp only [shift, map_sub]
    ring
  right_inv p := by
    apply Subtype.ext
    change shift s (b-a) (shift s (a-b) p.val) = p.val
    simp only [shift, map_sub]
    ring

def observedValues (s : Finset F) {t : Nat} {secret : F}
    (p : SecretPolynomials t secret) : s → F := fun x => p.val.eval x.val

/-- Under the uniform polynomial law, fewer than t nonzero evaluations have
the same distribution for every secret. The implementation's biased byte
sampler must still be connected and its statistical distance accounted for. -/
theorem uniform_shares_secret_independent [Finite F] (s : Finset F)
    (nonzero : (0 : F) ∉ s) (t : Nat) (few : s.card < t) (a b : F)
    (event : Set (s → F)) :
    uniformOn (Set.univ : Set (SecretPolynomials t a)) {p | observedValues s p ∈ event} =
      uniformOn (Set.univ : Set (SecretPolynomials t b)) {p | observedValues s p ∈ event} := by
  let e := secretEquiv s nonzero t few a b
  have hobs (p : SecretPolynomials t a) : observedValues s (e p) = observedValues s p := by
    funext x
    exact shift_observed s nonzero (b-a) p.val x.val x.property
  have hevent : {p : SecretPolynomials t a | observedValues s p ∈ event} =
      e ⁻¹' {p : SecretPolynomials t b | observedValues s p ∈ event} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hobs]
  rw [hevent]
  exact uniform_event_equiv e _

/-- Simultaneous transport for every polynomial in a finite family. This
covers all limbs jointly under the uniform polynomial-table law, rather than
assuming that scalar secrecy alone implies joint secrecy. -/
theorem uniform_joint_shares_secret_independent [Finite F] {I : Type} [Fintype I]
    (s : I → Finset F) (nonzero : ∀ j, (0 : F) ∉ s j)
    (t : I → Nat) (few : ∀ j, (s j).card < t j) (a b : I → F)
    (event : Set ((j : I) → s j → F)) :
    uniformOn (Set.univ : Set ((j : I) → SecretPolynomials (t j) (a j)))
      {p | (fun j => observedValues (s j) (p j)) ∈ event} =
    uniformOn (Set.univ : Set ((j : I) → SecretPolynomials (t j) (b j)))
      {p | (fun j => observedValues (s j) (p j)) ∈ event} := by
  let e := Equiv.piCongrRight fun j => secretEquiv (s j) (nonzero j) (t j) (few j) (a j) (b j)
  have hobs (p : (j : I) → SecretPolynomials (t j) (a j)) :
      (fun j => observedValues (s j) (e p j)) = (fun j => observedValues (s j) (p j)) := by
    funext j x
    exact shift_observed (s j) (nonzero j) (b j-a j) (p j).val x.val x.property
  have hevent : {p : (j : I) → SecretPolynomials (t j) (a j) |
      (fun j => observedValues (s j) (p j)) ∈ event} =
      e ⁻¹' {p : (j : I) → SecretPolynomials (t j) (b j) |
        (fun j => observedValues (s j) (p j)) ∈ event} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hobs]
  rw [hevent]
  exact uniform_event_equiv e _

end WotsLamport.Submission.Shamir
