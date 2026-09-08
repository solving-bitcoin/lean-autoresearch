import G1Release.Submission.Certificate

namespace G1Release.Submission.Privacy

open G1Release.Protected
open G1Release.Submission.Scheme
open SecretRelease
open MeasureTheory ProbabilityTheory

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem keys_measurableSet (s : Set challenge.inputs.Keys) :
    MeasurableSet s :=
  MeasurableSpace.measurableSet_top

theorem outputs_measurableSet (s : Set challenge.outputs.Keys) :
    MeasurableSet s :=
  MeasurableSpace.measurableSet_top

theorem coins_measurableSet (s : Set (SecretRelease.Bytes scheme.randomnessBytes)) :
    MeasurableSet s :=
  MeasurableSpace.measurableSet_top

end G1Release.Submission.Privacy
