import Blake3Prize.Protected.Target
import SecretRelease.Runtime

namespace Blake3Prize.Protected
open SecretRelease (Codec)

def wire : SecretRelease.WireFormat challenge where
  identity := "blake3-64-release-v1"
  inputs := .lamport (Codec.byteVector 64)
  outputs := .lamport (Codec.byteVector 32)
  output := some (Codec.byteVector 32).bytes
end Blake3Prize.Protected
