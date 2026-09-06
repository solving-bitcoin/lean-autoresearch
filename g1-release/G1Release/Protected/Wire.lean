import G1Release.Protected.Target
import SecretRelease.Runtime

namespace G1Release.Protected
open SecretRelease

def wire : WireFormat challenge where
  identity := "g1-release-v1"
  inputs := .lamport inputCodec
  outputs := .plain encodeOutput
  output := some outputCodec.bytes
end G1Release.Protected
