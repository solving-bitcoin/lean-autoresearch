import Blake3Prize.Protected.Target
import SecretRelease.Runtime

namespace Blake3Prize.Protected

def wire : SecretRelease.WireFormat challenge where
  identity := "blake3-64-release-v1"
  inputs := .lamport (bitCodec 512)
  outputs := .lamport (bitCodec 256)
  output := some (bitCodec 256).bytes
end Blake3Prize.Protected
