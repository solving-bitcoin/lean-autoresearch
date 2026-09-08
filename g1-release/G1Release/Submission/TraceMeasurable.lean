import G1Release.Submission.GameViews

namespace G1Release.Submission.TraceMeasurable
open SecretRelease G1Release.Protected Randomized RealIdeal
open MeasureTheory OracleComp MeasurableModels

instance : MeasurableSpace (List ByteArray) := ⊤
local instance : Countable challenge.Input := by change Countable Input; infer_instance

theorem queries_measurable (program : Program α) :
    Measurable (fun h : ROM.Oracle => ROMTrace.queries (ROM.hash h) program) := by
  induction program using OracleComp.inductionOn with
  | pure value => exact measurable_const
  | query_bind t k ih =>
    have hc : Measurable (fun p : ROM.Oracle × Label => ROMTrace.queries (ROM.hash p.1) (k p.2)) :=
      measurable_from_prod_countable_left ih
    exact (Measurable.of_discrete : Measurable (List.cons t)).comp
      (hc.comp (measurable_id.prodMk (ROMTrace.hash_measurable t)))

theorem queries_variable_measurable {I : Type} [MeasurableSpace I]
    [Countable I] [MeasurableSingletonClass I] (program : I → Program α) :
    Measurable (fun p : I × ROM.Oracle => ROMTrace.queries (ROM.hash p.2) (program p.1)) :=
  measurable_from_prod_countable_right fun i => queries_measurable (program i)

theorem ideal_trace_measurable (hidden : Hidden) (random : Randomness hidden) (input : Input)
    (active : Fin 512 → Label) (adversary : View challenge → Program α) :
    Measurable (fun oracle : ExtendedOracle => ROMTrace.queries (ROM.hash (baseOracle oracle))
      (adversary (GameViews.ideal hidden random input active oracle))) :=
  (queries_variable_measurable adversary).comp
    ((GameViews.ideal_measurable hidden random input active).prodMk
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _))

end G1Release.Submission.TraceMeasurable
