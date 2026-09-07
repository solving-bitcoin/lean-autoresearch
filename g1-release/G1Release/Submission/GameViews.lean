import G1Release.Submission.GarbleMeasurable

namespace G1Release.Submission.GameViews
open SecretRelease G1Release.Protected Randomized RealIdeal
open MeasureTheory MeasurableModels

local instance : Countable challenge.Input := by
  change Countable Input
  infer_instance

def make (hidden : Hidden) (input : Input) (active : Fin 512 → Label)
    (artifact : ByteArray) : View challenge :=
  ⟨input,artifact,pack ((List.finRange 512).map active),encodeOutput (reference hidden input)⟩

def real (hash : Hash) (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) : View challenge :=
  make hidden input (selected keys input) (Scheme.encode (Randomized.garble hash hidden random keys))

def ideal (hidden : Hidden) (random : Randomness hidden) (input : Input)
    (active : Fin 512 → Label) (oracle : ExtendedOracle) : View challenge :=
  make hidden input active (IdealView.garble (ROM.hash (baseOracle oracle)) input hidden random
    active (fakeCiphertexts oracle))

theorem real_programmed (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (oracle : ExtendedOracle) :
    real (ROM.hash (programmed hidden random keys input oracle)) hidden random keys input =
      ideal hidden random input (selected keys input) oracle := by
  unfold real ideal
  rw [RealIdeal.garble_programmed]

theorem ideal_coupled (source target : Hidden) (input : Input)
    (hequal : OffsetFamily.mapAt source input = OffsetFamily.mapAt target input)
    (href : reference source input = reference target input)
    (random : Randomness source) (active : Fin 512 → Label) (oracle : ExtendedOracle) :
    ideal source random input active oracle =
      ideal target (targetRandomness input source target hequal random) input active oracle := by
  unfold ideal
  rw [IdealView.garble_preserved _ input source target hequal random]
  unfold make
  rw [href]

theorem real_measurable (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) :
    Measurable (fun oracle : ROM.Oracle => real (ROM.hash oracle) hidden random keys input) :=
  (Measurable.of_discrete : Measurable (make hidden input (selected keys input))).comp
    (GarbleMeasurable.garble_measurable ROM.hash ROMTrace.hash_measurable hidden random keys)

theorem ideal_measurable (hidden : Hidden) (random : Randomness hidden) (input : Input)
    (active : Fin 512 → Label) : Measurable (ideal hidden random input active) :=
  (Measurable.of_discrete : Measurable (make hidden input active)).comp
    (GarbleMeasurable.ideal_measurable (fun oracle => ROM.hash (baseOracle oracle))
      (fun _ => measurable_pi_apply _) hidden random input active fakeCiphertexts
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _))

theorem real_run_measurable [MeasurableSpace α] (hidden : Hidden) (random : Randomness hidden)
    (keys : Fin 512 → Pair) (input : Input) (adversary : View challenge → Program α) :
    Measurable (fun oracle : ROM.Oracle =>
      ROM.run (ROM.hash oracle) (adversary (real (ROM.hash oracle) hidden random keys input))) :=
  (run_variable_measurable adversary).comp
    ((real_measurable hidden random keys input).prodMk measurable_id)

theorem ideal_run_measurable [MeasurableSpace α] (hidden : Hidden) (random : Randomness hidden)
    (input : Input) (active : Fin 512 → Label) (adversary : View challenge → Program α) :
    Measurable (fun oracle : ExtendedOracle => ROM.run (ROM.hash (baseOracle oracle))
      (adversary (ideal hidden random input active oracle))) :=
  (run_variable_measurable adversary).comp
    ((ideal_measurable hidden random input active).prodMk
      (measurable_pi_lambda _ fun _ => measurable_pi_apply _))

theorem protected_view_eq (n : Nat)
    (sampler : SecretRelease.Bytes n → (hidden : Hidden) → Randomness hidden)
    (hidden : Hidden) (input : Input) (ω : ROM.Sample (Randomized.scheme n sampler)) :
    ROM.view (Randomized.scheme n sampler) hidden input ω =
      real (ROM.hash ω.2.2.2) hidden (sampler ω.2.2.1 hidden) ω.1 input := rfl

end G1Release.Submission.GameViews
