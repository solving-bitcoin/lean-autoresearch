import WotsLamport.Protected.Wire
namespace WotsLamport.Tests
open SecretRelease Protected
example (h : Hash) (keys : Keys) (m : Message) :
    verifies h (publicKey h keys) (encodeWord m) (sign h keys m) := sign_verifies h keys m
example (h : Hash) (keys : Keys) (m : Message) :
    extract (canonicalSign h keys m) = some m := extract_sign h keys m
example : challenge.withholding.isSome = true := rfl
end WotsLamport.Tests
