import G1Release.Submission.CosetGameViews
import G1Release.Submission.TraceMeasurable

namespace G1Release.Submission.CosetTraceMeasurable
open SecretRelease G1Release.Protected CosetSampler CosetSlots CosetRealIdeal
open MeasureTheory OracleComp MeasurableModels

local instance : Countable challenge.Input := by change Countable Input; infer_instance

theorem ideal_trace_measurable (hidden : Hidden) (random : Randomness hidden) (input : Input)
    (active : Fin 512 → Label) (adversary : View challenge → Program α) :
    Measurable (fun oracle : ExtendedOracle => ROMTrace.queries (ROM.hash (baseOracle oracle))
      (adversary (CosetGameViews.ideal hidden random input active oracle))) :=
  (TraceMeasurable.queries_variable_measurable adversary).comp
    ((CosetGameViews.ideal_measurable hidden random input active).prodMk
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _))

end G1Release.Submission.CosetTraceMeasurable
