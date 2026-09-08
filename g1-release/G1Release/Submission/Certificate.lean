import G1Release.Submission.SchemeCert

namespace G1Release.Submission.Certificate

open G1Release.Protected
open G1Release.Submission.Scheme
open SecretRelease

set_option maxHeartbeats 800000
set_option maxRecDepth 4096

theorem withholdingSecure : ROM.WithholdingSecure scheme := by
  simp [ROM.WithholdingSecure, challenge]

theorem artifactBound_all : ArtifactBound scheme claimedBytes :=
  fun h coins p ik ok => artifactBound h coins p ik ok

theorem decode_encode_all (artifact : scheme.Artifact) :
    scheme.decode (scheme.encode artifact) = some artifact := by
  rw [scheme_encode, scheme_decode]
  exact decode_encode artifact

theorem encode_decode_all {bytes : ByteArray} {artifact : scheme.Artifact}
    (h : scheme.decode bytes = some artifact) :
    scheme.encode artifact = bytes := by
  rw [scheme_decode] at h
  rw [scheme_encode]
  exact encode_decode h

end G1Release.Submission.Certificate
