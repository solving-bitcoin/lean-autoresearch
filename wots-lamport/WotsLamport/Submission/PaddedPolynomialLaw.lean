import WotsLamport.Submission.PolynomialLaw

namespace WotsLamport.Submission.Shamir
open MeasureTheory ProbabilityTheory

variable {F : Type}

def coefficientPrefix {k n : Nat} (bound : k ≤ n) (c : Fin n → F) : Fin k → F :=
  fun j => c ⟨j.val, lt_of_lt_of_le j.isLt bound⟩

def replaceCoefficientPrefix {k n : Nat} (bound : k ≤ n)
    (e : (Fin k → F) ≃ (Fin k → F)) (c : Fin n → F) : Fin n → F :=
  fun j => if hj : j.val < k then e (coefficientPrefix bound c) ⟨j.val, hj⟩ else c j

theorem coefficientPrefix_replace {k n : Nat} (bound : k ≤ n)
    (e : (Fin k → F) ≃ (Fin k → F)) (c : Fin n → F) :
    coefficientPrefix bound (replaceCoefficientPrefix bound e c) = e (coefficientPrefix bound c) := by
  funext j
  simp [coefficientPrefix, replaceCoefficientPrefix, j.isLt]

/-- A bijection on the used coefficient prefix extends to allocated storage
without changing unused padding coefficients. -/
def paddedCoefficientEquiv {k n : Nat} (bound : k ≤ n)
    (e : (Fin k → F) ≃ (Fin k → F)) : (Fin n → F) ≃ (Fin n → F) where
  toFun := replaceCoefficientPrefix bound e
  invFun := replaceCoefficientPrefix bound e.symm
  left_inv c := by
    funext j
    change (if hj : j.val < k then e.symm
      (coefficientPrefix bound (replaceCoefficientPrefix bound e c)) ⟨j.val, hj⟩
      else replaceCoefficientPrefix bound e c j) = c j
    by_cases hj : j.val < k
    · rw [dif_pos hj, coefficientPrefix_replace, Equiv.symm_apply_apply]
      rfl
    · simp [hj, replaceCoefficientPrefix]
  right_inv c := by
    funext j
    change (if hj : j.val < k then e
      (coefficientPrefix bound (replaceCoefficientPrefix bound e.symm c)) ⟨j.val, hj⟩
      else replaceCoefficientPrefix bound e.symm c j) = c j
    by_cases hj : j.val < k
    · rw [dif_pos hj, coefficientPrefix_replace, Equiv.apply_symm_apply]
      rfl
    · simp [hj, replaceCoefficientPrefix]

variable [Field F] [DecidableEq F]

noncomputable def coefficientSecretEquiv (s : Finset F) (nonzero : (0 : F) ∉ s)
    (k : Nat) (few : s.card < k+1) (a b : F) : (Fin k → F) ≃ (Fin k → F) :=
  (coefficientEquiv a k).trans
    ((secretEquiv s nonzero (k+1) few a b).trans (coefficientEquiv b k).symm)

theorem coefficientSecretEquiv_observed (s : Finset F) (nonzero : (0 : F) ∉ s)
    (k : Nat) (few : s.card < k+1) (a b : F) (c : Fin k → F) :
    observedValues s (coefficientEquiv b k (coefficientSecretEquiv s nonzero k few a b c)) =
      observedValues s (coefficientEquiv a k c) := by
  change observedValues s (coefficientEquiv b k ((coefficientEquiv b k).symm
    (secretEquiv s nonzero (k+1) few a b (coefficientEquiv a k c)))) = _
  rw [Equiv.apply_symm_apply]
  funext x
  exact shift_observed s nonzero (b-a) _ x.val x.property

/-- Joint privacy for full allocated coefficient vectors, including unused
padding. No independence conclusion is inferred from separate scalar events. -/
theorem uniform_padded_joint_secret_independent [Finite F] [MeasurableSpace F]
    [DiscreteMeasurableSpace F] {I : Type} [Fintype I]
    (n : Nat) (k : I → Nat) (bound : ∀ j, k j ≤ n)
    (s : I → Finset F) (nonzero : ∀ j, (0 : F) ∉ s j)
    (few : ∀ j, (s j).card < k j+1) (a b : I → F)
    (event : Set ((j : I) → s j → F)) :
    uniformOn (Set.univ : Set (I → Fin n → F))
      {c | (fun j => observedValues (s j)
        (coefficientEquiv (a j) (k j) (coefficientPrefix (bound j) (c j)))) ∈ event} =
    uniformOn (Set.univ : Set (I → Fin n → F))
      {c | (fun j => observedValues (s j)
        (coefficientEquiv (b j) (k j) (coefficientPrefix (bound j) (c j)))) ∈ event} := by
  let e := Equiv.piCongrRight fun j => paddedCoefficientEquiv (bound j)
    (coefficientSecretEquiv (s j) (nonzero j) (k j) (few j) (a j) (b j))
  have hobs (c : I → Fin n → F) :
      (fun j => observedValues (s j) (coefficientEquiv (b j) (k j)
        (coefficientPrefix (bound j) (e c j)))) =
      (fun j => observedValues (s j) (coefficientEquiv (a j) (k j)
        (coefficientPrefix (bound j) (c j)))) := by
    funext j
    change observedValues (s j) (coefficientEquiv (b j) (k j)
      (coefficientPrefix (bound j) (replaceCoefficientPrefix (bound j) _ (c j)))) = _
    rw [coefficientPrefix_replace]
    exact coefficientSecretEquiv_observed (s j) (nonzero j) (k j) (few j) (a j) (b j) (coefficientPrefix (bound j) (c j))
  have hevent :
      {c : I → Fin n → F | (fun j => observedValues (s j)
        (coefficientEquiv (a j) (k j) (coefficientPrefix (bound j) (c j)))) ∈ event} =
      e ⁻¹' {c | (fun j => observedValues (s j)
        (coefficientEquiv (b j) (k j) (coefficientPrefix (bound j) (c j)))) ∈ event} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hobs]
  rw [hevent]
  exact uniform_event_equiv e _


/-- Unchanged secrets require no threshold restriction. This permits a joint
hybrid which changes opposite labels while retaining every selected label and
all of its visible evaluations. -/
theorem uniform_padded_joint_secret_transport [Finite F] [MeasurableSpace F]
    [DiscreteMeasurableSpace F] {I : Type} [Fintype I]
    (n : Nat) (k : I → Nat) (bound : ∀ j, k j ≤ n)
    (s : I → Finset F) (nonzero : ∀ j, (0 : F) ∉ s j)
    (a b : I → F) (valid : ∀ j, a j = b j ∨ (s j).card < k j+1)
    (event : Set ((j : I) → s j → F)) :
    uniformOn (Set.univ : Set (I → Fin n → F))
      {c | (fun j => observedValues (s j)
        (coefficientEquiv (a j) (k j) (coefficientPrefix (bound j) (c j)))) ∈ event} =
    uniformOn (Set.univ : Set (I → Fin n → F))
      {c | (fun j => observedValues (s j)
        (coefficientEquiv (b j) (k j) (coefficientPrefix (bound j) (c j)))) ∈ event} := by
  classical
  let localEquiv (j : I) : (Fin n → F) ≃ (Fin n → F) :=
    if he : a j = b j then Equiv.refl _ else
      paddedCoefficientEquiv (bound j) (coefficientSecretEquiv (s j) (nonzero j)
        (k j) ((valid j).resolve_left he) (a j) (b j))
  let e := Equiv.piCongrRight localEquiv
  have hobs (c : I → Fin n → F) :
      (fun j => observedValues (s j) (coefficientEquiv (b j) (k j)
        (coefficientPrefix (bound j) (e c j)))) =
      (fun j => observedValues (s j) (coefficientEquiv (a j) (k j)
        (coefficientPrefix (bound j) (c j)))) := by
    funext j
    by_cases he : a j = b j
    · simp [e, localEquiv, he]
    · change observedValues (s j) (coefficientEquiv (b j) (k j)
        (coefficientPrefix (bound j) (localEquiv j (c j)))) = _
      simp only [localEquiv, dif_neg he]
      change observedValues (s j) (coefficientEquiv (b j) (k j)
        (coefficientPrefix (bound j) (replaceCoefficientPrefix (bound j) _ (c j)))) = _
      rw [coefficientPrefix_replace]
      exact coefficientSecretEquiv_observed (s j) (nonzero j) (k j)
        ((valid j).resolve_left he) (a j) (b j) (coefficientPrefix (bound j) (c j))
  have hevent :
      {c : I → Fin n → F | (fun j => observedValues (s j)
        (coefficientEquiv (a j) (k j) (coefficientPrefix (bound j) (c j)))) ∈ event} =
      e ⁻¹' {c | (fun j => observedValues (s j)
        (coefficientEquiv (b j) (k j) (coefficientPrefix (bound j) (c j)))) ∈ event} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hobs]
  rw [hevent]
  exact uniform_event_equiv e _

end WotsLamport.Submission.Shamir
