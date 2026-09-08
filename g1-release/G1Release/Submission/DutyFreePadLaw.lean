import G1Release.Submission.DutyFreeViewCoupling
import G1Release.Submission.EventBounds

/-! The exceptional raw-pad tail is counted in the actual finite space of
two 256-bit answers. A union bound covers all 728 × 64 selected field pads;
no independence between failure events is needed for this bound. -/
namespace G1Release.Submission.DutyFreePadLaw
open MeasureTheory ProbabilityTheory SecretRelease GarblingPrize.Protected
open DutyFreeLayout DutyFreeIdeal
set_option exponentiation.threshold 1024

theorem finite_pi_uniform {ι β : Type*} [Fintype ι] [MeasurableSpace β]
    [DiscreteMeasurableSpace β] [Finite β] [Nonempty β] :
    (Measure.infinitePi fun _ : ι => uniformOn (Set.univ : Set β)) =
      uniformOn (Set.univ : Set (ι → β)) := by
  rw [Measure.infinitePi_eq_pi, ← uniformOn_pi (f := fun _ : ι => (Set.univ : Set β))]
  simp

theorem eval_preserving {ι β : Type*} [Fintype ι] [MeasurableSpace β]
    [DiscreteMeasurableSpace β] [Finite β] [Nonempty β] (i : ι) :
    MeasurePreserving (fun values : ι → β => values i)
      (uniformOn Set.univ) (uniformOn Set.univ) := by
  rw [← finite_pi_uniform]
  exact measurePreserving_eval_infinitePi _ i

theorem raw_card : Nat.card DutyFreeFieldPad.Raw = 2^512 := by
  simpa only [Nat.card_fin] using Nat.card_congr DutyFreeFieldPad.rawEquiv

theorem raw_bad_bound :
    uniformOn (Set.univ : Set DutyFreeFieldPad.Raw) DutyFreeFieldPad.bad ≤
      (baseFieldModulus : ENNReal) / 2^512 := by
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)).mp
  rw [FiniteProbability.uniform_real, DutyFreeFieldPad.bad_card, raw_card]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_pow,
    ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  apply div_le_div_of_nonneg_right
  · exact_mod_cast (Nat.mod_lt (2^512) (by decide : 0 < baseFieldModulus)).le
  · positivity

def bad : Set PlainPads := {pads | ¬DutyFreeViewCoupling.good pads}

theorem bad_bound : uniformOn (Set.univ : Set PlainPads) bad ≤
    (46592 : ENNReal) * ((baseFieldModulus : ENNReal) / 2^512) := by
  classical
  have hs : bad = ⋃ table : Table, ⋃ chunk : Chunk,
      {pads : PlainPads | pads table chunk ∈ DutyFreeFieldPad.bad} := by
    ext pads
    simp only [bad, DutyFreeViewCoupling.good, Set.mem_setOf_eq, not_forall,
      Classical.not_not, Set.mem_iUnion]
  rw [hs]
  apply (measure_iUnion_le _).trans
  calc
    (∑' table : Table, uniformOn Set.univ (⋃ chunk : Chunk,
        {pads : PlainPads | pads table chunk ∈ DutyFreeFieldPad.bad})) ≤
      ∑' _ : Table, ∑' _ : Chunk, (baseFieldModulus : ENNReal) / 2^512 := by
      apply ENNReal.tsum_le_tsum
      intro table
      apply (measure_iUnion_le _).trans
      apply ENNReal.tsum_le_tsum
      intro chunk
      have hm := (eval_preserving (β := DutyFreeFieldPad.Raw) chunk).comp
        (eval_preserving (β := Chunk → DutyFreeFieldPad.Raw) table)
      exact (hm.measure_preimage
        (MeasurableSet.of_discrete : MeasurableSet DutyFreeFieldPad.bad).nullMeasurableSet).trans_le
        raw_bad_bound
    _ = _ := by norm_num [tsum_fintype, ← mul_assoc]

theorem bad_small : (46592 : ENNReal) * ((baseFieldModulus : ENNReal) / 2^512) ≤
    (1 : ENNReal) / 2^240 := by
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  norm_num [baseFieldModulus, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow]

end G1Release.Submission.DutyFreePadLaw
