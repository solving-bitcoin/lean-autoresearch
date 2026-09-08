/-! Trusted runtime primitive, deliberately absent from the certificate imports.
The ideal-ROM theorem does not prove this SHA-256 instantiation secure. -/
namespace SecretRelease
@[extern "lean_secret_release_sha256"]
opaque sha256 : ByteArray → ByteArray

def nativeHash (bytes : ByteArray) : Vector UInt8 32 :=
  let digest := sha256 bytes
  if h : digest.size = 32 then ⟨digest.data, h⟩ else Vector.replicate 32 0
end SecretRelease
