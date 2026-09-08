import G1Release.Submission.DutyFreeGarbleMeasurable
import G1Release.Submission.CosetSampler

namespace G1Release.Submission.DutyFreeGameViews
open SecretRelease G1Release.Protected DutyFreeSlots DutyFreeRealIdeal
open MeasureTheory MeasurableModels
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

local instance : Countable challenge.Input := by
  change Countable Input
  infer_instance

def make (hidden : Private) (input : Input) (active : DutyFreeIdeal.Active)
    (artifact : ByteArray) : View challenge :=
  ⟨input,artifact,pack ((List.finRange 512).map active),encodeOutput (reference hidden input)⟩

def real (hash : Hash) (hidden : Private) (random : CosetSampler.Randomness hidden)
    (keys : Keys) (hot : HotKeys) (input : Input) : View challenge :=
  make hidden input (active keys input)
    (DutyFreeArtifact.encode (DutyFreeProgram.garble hash hidden random.1 keys hot))

def ideal (hidden : Private) (random : CosetSampler.Randomness hidden) (input : Input)
    (active : DutyFreeIdeal.Active) (hot : HotKeys) (oracle : ExtendedOracle) : View challenge :=
  make hidden input active (DutyFreeArtifact.encode (DutyFreeIdeal.garble (ROM.hash (base oracle))
    input hidden random.1 active hot (bridgePads oracle) (plainPads oracle)))

theorem real_programmed (hidden : Private) (random : CosetSampler.Randomness hidden)
    (keys : Keys) (hot : HotKeys) (input : Input) (oracle : ExtendedOracle) :
    real (ROM.hash (programmed keys hot input oracle)) hidden random keys hot input =
      ideal hidden random input (active keys input) hot oracle := by
  unfold real ideal
  rw [garble_programmed]

theorem real_measurable (hidden : Private) (random : CosetSampler.Randomness hidden)
    (keys : Keys) (hot : HotKeys) (input : Input) :
    Measurable (fun oracle : ROM.Oracle => real (ROM.hash oracle) hidden random keys hot input) :=
  (Measurable.of_discrete : Measurable (make hidden input (active keys input))).comp
    (DutyFreeGarbleMeasurable.real_measurable ROM.hash ROMTrace.hash_measurable hidden random.1 keys hot)

theorem ideal_measurable (hidden : Private) (random : CosetSampler.Randomness hidden)
    (input : Input) (active : DutyFreeIdeal.Active) (hot : HotKeys) :
    Measurable (ideal hidden random input active hot) :=
  (Measurable.of_discrete : Measurable (make hidden input active)).comp
    (DutyFreeGarbleMeasurable.ideal_measurable (fun oracle => ROM.hash (base oracle))
      (fun _ => measurable_pi_apply _) hidden random.1 input active hot bridgePads
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _) plainPads
      (measurable_pi_lambda _ fun _ => measurable_pi_lambda _ fun _ =>
        (measurable_pi_apply _).prodMk (measurable_pi_apply _)))

theorem real_run_measurable [MeasurableSpace α] (hidden : Private)
    (random : CosetSampler.Randomness hidden) (keys : Keys) (hot : HotKeys) (input : Input)
    (adversary : View challenge → Program α) :
    Measurable (fun oracle : ROM.Oracle => ROM.run (ROM.hash oracle)
      (adversary (real (ROM.hash oracle) hidden random keys hot input))) :=
  (run_variable_measurable adversary).comp
    ((real_measurable hidden random keys hot input).prodMk measurable_id)

theorem ideal_run_measurable [MeasurableSpace α] (hidden : Private)
    (random : CosetSampler.Randomness hidden) (input : Input)
    (active : DutyFreeIdeal.Active) (hot : HotKeys) (adversary : View challenge → Program α) :
    Measurable (fun oracle : ExtendedOracle => ROM.run (ROM.hash (base oracle))
      (adversary (ideal hidden random input active hot oracle))) :=
  (run_variable_measurable adversary).comp
    ((ideal_measurable hidden random input active hot).prodMk
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _))

end G1Release.Submission.DutyFreeGameViews
