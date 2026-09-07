import SecretRelease

/-! Deterministic traces for the exact interpreter used by the protected
games. These lemmas support an identical-until-secret-query reduction. -/
namespace G1Release.Submission.ROMTrace
open SecretRelease OracleComp OracleSpec MeasureTheory
open scoped OracleSpec.PrimitiveQuery

def queries (hash : Hash) (program : Program α) : List ByteArray :=
  OracleComp.construct (fun _ => []) (fun t _ tails => t :: tails (hash t)) program

@[simp] theorem queries_pure (hash : Hash) (value : α) :
    queries hash (pure value) = [] := rfl

@[simp] theorem queries_bind (hash : Hash) (t : ByteArray) (k : Label → Program α) :
    queries hash ((liftM ((ByteArray →ₒ Label).query t) : Program Label) >>= k) = t :: queries hash (k (hash t)) := rfl

@[simp] theorem run_pure (hash : Hash) (value : α) :
    ROM.run hash (pure value) = value := rfl

@[simp] theorem run_bind (hash : Hash) (t : ByteArray) (k : Label → Program α) :
    ROM.run hash ((liftM ((ByteArray →ₒ Label).query t) : Program Label) >>= k) = ROM.run hash (k (hash t)) := rfl

theorem queries_length_le (hash : Hash) (program : Program α) (q : Nat)
    (hbound : IsTotalQueryBound program q) : (queries hash program).length ≤ q := by
  induction program using OracleComp.inductionOn generalizing q with
  | pure value => simp
  | query_bind t k ih =>
    rcases isTotalQueryBound_query_bind_iff.mp hbound with ⟨hpos,hk⟩
    have hrest := ih (hash t) (q-1) (hk (hash t))
    simp only [queries_bind, List.length_cons]
    omega

/-- A changed oracle cannot affect the result before the original execution
queries a changed address. The second execution need not be separately bounded. -/
theorem run_eq_of_agree (left right : Hash) (program : Program α)
    (h : ∀ t ∈ queries left program, left t = right t) :
    ROM.run left program = ROM.run right program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind t k ih =>
    have ht := h t (by simp)
    simp only [run_bind, ← ht]
    exact ih (left t) fun u hu => h u (by simp [hu])

theorem queries_eq_of_agree (left right : Hash) (program : Program α)
    (h : ∀ t ∈ queries left program, left t = right t) :
    queries left program = queries right program := by
  induction program using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind t k ih =>
    have ht := h t (by simp)
    simp only [queries_bind, ← ht]
    congr 1
    exact ih (left t) fun u hu => h u (by simp [hu])

theorem hash_measurable (t : ByteArray) : Measurable (fun h : ROM.Oracle => ROM.hash h t) :=
  measurable_pi_apply _

/-- No measurability assumption about the adversary's local computation is
needed for a fixed program: each oracle answer has a finite discrete range. -/
theorem run_measurable [MeasurableSpace α] (program : Program α) :
    Measurable (fun h : ROM.Oracle => ROM.run (ROM.hash h) program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact measurable_const
  | query_bind t k ih =>
    have hcont : Measurable (fun p : ROM.Oracle × Label => ROM.run (ROM.hash p.1) (k p.2)) :=
      measurable_from_prod_countable_left ih
    exact hcont.comp (measurable_id.prodMk (hash_measurable t))

end G1Release.Submission.ROMTrace
