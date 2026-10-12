import WotsLamport.Protected.Target
import SecretRelease.Runtime

namespace WotsLamport.Protected
open SecretRelease

def wire : WireFormat challenge where
  identity := "wots-lamport-base16-sha256-fullwidth-rom-v1"
  inputs := ⟨keyCodec, "wots-base16-seeds", 67⟩
  outputs := .lamport outputCodec
  output := some outputCodec.bytes
end WotsLamport.Protected
