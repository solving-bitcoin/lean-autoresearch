import G1Release.Submission.SchemeFinal

namespace G1Release.Submission.Scheme
open SecretRelease
open G1Release.Protected

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem correct : Correct scheme := by
  intro hash coins p ik ok x
  delta SecretRelease.Scheme.evaluateBytes SecretRelease.Scheme.garbleBytes
  erw [scheme_garble, scheme_encode, scheme_decode, decode_encode]
  erw [Option.bind_some, scheme_evaluate, evaluate_garble]
  rfl

end G1Release.Submission.Scheme
