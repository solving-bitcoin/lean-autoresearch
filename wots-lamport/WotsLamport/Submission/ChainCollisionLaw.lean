import WotsLamport.Submission.ChainTape
import WotsLamport.Submission.MultiTargetTrace
import WotsLamport.Submission.CoinEncoding
import Mathlib.Data.Fintype.Sigma

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory

noncomputable def collisionFiberEquiv {I A : Type} (i j : I) (different : i ≠ j) :
    {f : I → A // f i = f j} ≃ ({k : I // k ≠ i} → A) := by
  classical
  exact {
    toFun := fun f k => f.val k.val
    invFun := fun g => ⟨fun k => if hk : k = i then g ⟨j, different.symm⟩ else g ⟨k,hk⟩,
      by simp [different.symm]⟩
    left_inv := by
      intro f
      apply Subtype.ext
      funext k
      by_cases hk : k = i
      · subst k; simpa using f.property.symm
      · simp [hk]
    right_inv := by
      intro g
      funext k
      simp [k.property] }

theorem uniform_coordinate_collision {I A : Type} [Fintype I] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] (i j : I) (different : i ≠ j) :
    uniformOn (Set.univ : Set (I → A)) {f | f i = f j} =
      1 / (Fintype.card A : ENNReal) := by
  classical
  have hcard : Fintype.card {f : I → A // f i = f j} =
      Fintype.card A ^ (Fintype.card I-1) := by
    rw [Fintype.card_congr (collisionFiberEquiv (A := A) i j different)]
    simp
  have hi : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  have ha : Fintype.card A ≠ 0 := Fintype.card_ne_zero
  have hp : Fintype.card A ^ (Fintype.card I-1) ≠ 0 := pow_ne_zero _ ha
  have hsplit : Fintype.card A ^ Fintype.card I =
      Fintype.card A ^ (Fintype.card I-1) * Fintype.card A := by
    conv_lhs => rw [show Fintype.card I = (Fintype.card I-1)+1 by omega]
    rw [pow_succ]
  rw [uniformOn_univ, Measure.count_apply MeasurableSet.of_discrete,
    Set.encard, ENat.card_eq_coe_fintype_card]
  change (Fintype.card {f : I → A // f i = f j} : ENNReal) /
    (Fintype.card (I → A) : ENNReal) = _
  rw [hcard, Fintype.card_fun, hsplit, Nat.cast_mul]
  simpa only [mul_one] using ENNReal.mul_div_mul_left 1 (Fintype.card A : ENNReal)
    (c := (Fintype.card A ^ (Fintype.card I-1) : Nat))
    (by exact_mod_cast hp) (by simp)

/-- An ordered-pair union bound for an actual uniform node table. This is an
ideal-tape statement; relating it to the real chain law remains separate. -/
theorem uniform_table_collision_bound {I A : Type} [Fintype I] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] :
    uniformOn (Set.univ : Set (I → A)) {f | ¬ Function.Injective f} ≤
      (Fintype.card I : ENNReal)^2 / (Fintype.card A : ENNReal) := by
  classical
  let μ := uniformOn (Set.univ : Set (I → A))
  let event : I × I → Set (I → A) := fun ij => {f | ij.1 ≠ ij.2 ∧ f ij.1 = f ij.2}
  have hs : {f : I → A | ¬ Function.Injective f} ⊆
      {f | ∃ ij ∈ (Finset.univ : Finset (I × I)), f ∈ event ij} := by
    intro f hbad
    by_contra hnone
    apply hbad
    intro i j he
    by_contra hne
    exact hnone ⟨(i,j), Finset.mem_univ _, hne, he⟩
  have bound (ij : I × I) : μ (event ij) ≤ 1/(Fintype.card A : ENNReal) := by
    by_cases hd : ij.1 = ij.2
    · simp [event, hd]
    · have he : event ij = {f | f ij.1 = f ij.2} := by ext f; simp [event, hd]
      rw [he, uniform_coordinate_collision ij.1 ij.2 hd]
      exact le_rfl
  calc
    _ ≤ μ {f | ∃ ij ∈ (Finset.univ : Finset (I × I)), f ∈ event ij} := measure_mono hs
    _ ≤ ∑ ij ∈ (Finset.univ : Finset (I × I)), 1/(Fintype.card A : ENNReal) :=
      measure_exists_finset_le μ event (fun _ => 1/(Fintype.card A : ENNReal))
        Finset.univ (fun ij _ => bound ij)
    _ = _ := by simp [nsmul_eq_mul, pow_two, div_eq_mul_inv, mul_assoc]

theorem chainPosition_card : Fintype.card ChainPosition = 1056 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  decide +kernel

theorem uniform_chainTape_collision_bound :
    uniformOn (Set.univ : Set ChainTape) {tape | ¬ Function.Injective tape} ≤
      (1056 : ENNReal)^2 / 2^256 := by
  classical
  letI := Fintype.ofFinite Label
  have hlabel : Fintype.card Label = 2^256 := by rw [bytes_card]; norm_num
  simpa only [chainPosition_card, hlabel, Nat.cast_pow, Nat.cast_ofNat] using
    (uniform_table_collision_bound (I := ChainPosition) (A := Label))

end WotsLamport.Submission
