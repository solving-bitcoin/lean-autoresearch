import WotsLamport.Submission.ChainCollisionLaw
import WotsLamport.Submission.QueryTargets

namespace WotsLamport.Submission
open SecretRelease MeasureTheory ProbabilityTheory OracleComp

noncomputable def coordinateFiberEquiv {I A : Type} (i : I) (a : A) :
    {f : I → A // f i = a} ≃ ({k : I // k ≠ i} → A) := by
  classical
  exact {
    toFun := fun f k => f.val k.val
    invFun := fun g => ⟨fun k => if hk : k = i then a else g ⟨k,hk⟩, by simp⟩
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

theorem uniform_coordinate_mass {I A : Type} [Fintype I] [Fintype A] [Nonempty A]
    [MeasurableSpace A] [DiscreteMeasurableSpace A] (i : I) (a : A) :
    uniformOn (Set.univ : Set (I → A)) {f | f i = a} =
      1 / (Fintype.card A : ENNReal) := by
  classical
  have hcard : Fintype.card {f : I → A // f i = a} =
      Fintype.card A ^ (Fintype.card I-1) := by
    rw [Fintype.card_congr (coordinateFiberEquiv i a)]
    simp
  have hi : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨i⟩
  have hp : Fintype.card A ^ (Fintype.card I-1) ≠ 0 :=
    pow_ne_zero _ Fintype.card_ne_zero
  have hsplit : Fintype.card A ^ Fintype.card I =
      Fintype.card A ^ (Fintype.card I-1) * Fintype.card A := by
    conv_lhs => rw [show Fintype.card I = (Fintype.card I-1)+1 by omega]
    rw [pow_succ]
  rw [uniformOn_univ, Measure.count_apply MeasurableSet.of_discrete,
    Set.encard, ENat.card_eq_coe_fintype_card]
  change (Fintype.card {f : I → A // f i = a} : ENNReal) /
    (Fintype.card (I → A) : ENNReal) = _
  rw [hcard, Fintype.card_fun, hsplit, Nat.cast_mul]
  simpa only [mul_one] using ENNReal.mul_div_mul_left 1 (Fintype.card A : ENNReal)
    (c := (Fintype.card A ^ (Fintype.card I-1) : Nat))
    (by exact_mod_cast hp) (by simp)

/-- Concrete programming loss for a uniform ideal chain tape and a fixed
independent baseline/program. This does not assert that the programmed
oracle has the real chain law or permit a program that already sees the tape. -/
theorem ideal_chain_program_difference {A : Type} (baseline : Hash)
    (p : Program A) (q : Nat) (bound : IsTotalQueryBound p q) :
    uniformOn (Set.univ : Set ChainTape)
      {tape | ROM.run baseline p ≠ ROM.run (programChainOracle baseline tape) p} ≤
        (1056 : ENNReal) * q / 2^256 := by
  classical
  letI := Fintype.ofFinite Label
  have hlabel : Fintype.card Label = 2^256 := by rw [bytes_card]; norm_num
  have mass (position : ChainPosition) (label : Label) :
      uniformOn (Set.univ : Set ChainTape) {tape | tape position = label} ≤
        1/(2 : ENNReal)^256 := by
    simpa only [hlabel, Nat.cast_pow, Nat.cast_ofNat] using
      (uniform_coordinate_mass position label).le
  have off (tape : ChainTape) (input : ByteArray)
      (missing : ∀ position, chainQueryTarget input ≠ some (tape position)) :
      baseline input = programChainOracle baseline tape input := by
    apply (programChainOracle_off_tape baseline tape input ?_).symm
    intro edge he
    apply missing edge.val
    rw [← he]
    exact chainQueryTarget_complete (tape edge.val)
  have h := multi_target_run_difference_bound
    (uniformOn (Set.univ : Set ChainTape)) (fun position tape => tape position)
    (1/(2 : ENNReal)^256) mass (fun _ => chainQueryTarget) baseline
    (programChainOracle baseline) off p q bound
  simpa only [chainPosition_card, Nat.cast_ofNat, div_eq_mul_inv, one_mul, mul_assoc] using h

end WotsLamport.Submission
