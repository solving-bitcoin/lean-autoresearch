import WotsLamport.Protected.Target
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Ext

namespace WotsLamport.Submission
open SecretRelease OracleSpec OracleComp MeasureTheory

abbrev oracleQuery (input : ByteArray) : Program Label :=
  liftM ((ByteArray →ₒ Label).query input)

theorem run_query_bind {A : Type} (h : Hash) (input : ByteArray) (next : Label → Program A) :
    ROM.run h ((oracleQuery input : Program Label) >>= next) = ROM.run h (next (h input)) := by
  change evalWithAnswerFn (QueryImpl.ofFn h) ((oracleQuery input : Program Label) >>= next) =
    evalWithAnswerFn (QueryImpl.ofFn h) (next (h input))
  unfold oracleQuery
  rw [evalWithAnswerFn_bind]
  simp only [evalWithAnswerFn, simulateQ_spec_query, QueryImpl.ofFn_apply]

/-- Every total free oracle program with finite answers inspects a finite set
of possible query inputs across all executions. This set is not asserted to
have size at most the pathwise query budget. -/
theorem program_finite_query_support {A : Type} (p : Program A) :
    ∃ inputs : Finset ByteArray, ∀ h g : Hash,
      (∀ input ∈ inputs, h input = g input) → ROM.run h p = ROM.run g p := by
  classical
  letI := Fintype.ofFinite Label
  induction p using OracleComp.inductionOn with
  | pure a => exact ⟨∅, fun _ _ _ => rfl⟩
  | query_bind input next ih =>
    choose support agrees using ih
    refine ⟨insert input (Finset.univ.biUnion support), ?_⟩
    intro h g he
    rw [run_query_bind, run_query_bind, he input (Finset.mem_insert_self _ _)]
    apply agrees (g input) h g
    intro query hquery
    apply he query
    exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨g input, Finset.mem_univ _, hquery⟩)

noncomputable def completeAnswerTable (inputs : Finset ByteArray) (answers : inputs → Label) : Hash := by
  classical
  exact fun input => if hi : input ∈ inputs then answers ⟨input, hi⟩ else Vector.replicate 32 0

/-- Fixed adversarial programs are measurable under the protected infinite
random-function model, even though their query-input domain is unbounded. -/
theorem measurable_program_run {A : Type} [MeasurableSpace A] (p : Program A) :
    Measurable (fun oracle : ROM.Oracle => ROM.run (ROM.hash oracle) p) := by
  classical
  obtain ⟨inputs, agrees⟩ := program_finite_query_support p
  let restrict := fun oracle : ROM.Oracle => fun input : inputs => ROM.hash oracle input.val
  have hr : Measurable restrict := by
    apply measurable_pi_lambda
    intro input
    exact measurable_pi_apply _
  have he : (fun oracle : ROM.Oracle => ROM.run (ROM.hash oracle) p) =
      (fun answers : inputs → Label => ROM.run (completeAnswerTable inputs answers) p) ∘ restrict := by
    funext oracle
    apply agrees
    intro input hi
    simp only [completeAnswerTable, dif_pos hi, restrict]
  rw [he]
  exact Measurable.of_discrete.comp hr

/-- An arbitrary adversary may choose its program from a measurable countable
view. Its resulting execution remains measurable; no computability restriction
on the adversary's program-selection function is imposed. -/
theorem measurable_program_family {Ω V A : Type}
    [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    [MeasurableSpace A] (a : V → Program A) (oracle : Ω → ROM.Oracle) (view : Ω → V)
    (ho : Measurable oracle) (hv : Measurable view) :
    Measurable (fun ω => ROM.run (ROM.hash (oracle ω)) (a (view ω))) := by
  have hm : Measurable (fun pair : ROM.Oracle × V => ROM.run (ROM.hash pair.1) (a pair.2)) :=
    measurable_from_prod_countable_left (fun v => measurable_program_run (a v))
  exact hm.comp (ho.prodMk hv)

end WotsLamport.Submission
