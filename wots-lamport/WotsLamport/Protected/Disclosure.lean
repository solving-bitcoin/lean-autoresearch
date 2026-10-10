import WotsLamport.Protected.Chains

namespace WotsLamport.Protected
open SecretRelease

/-- The active channel is 67 correlated nodes in chain order (2,144 bytes).
The known 32-byte message supplies canonical selectors; it is not extra state. -/
def wotsDisclosure : Disclosure Message where
  Keys := Keys
  finite := inferInstance
  nonempty := inferInstance
  reveal := fun h keys m => signatureBytes (sign h keys m)

end WotsLamport.Protected
