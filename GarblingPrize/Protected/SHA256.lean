import GarblingPrize.Protected.Bytes

namespace GarblingPrize.Protected

/-!
# Native SHA-256 boundary

The benchmark executable obtains SHA-256 from the package's portable C
backend. These functions are not part of the ranked information-theoretic
privacy theorem, which samples the internal and label oracles ideally. Native
vectors test the linked backend, while concrete privacy treats HMAC-SHA256 as
an external PRF assumption.
-/

namespace SHA256

/-- Raw native digest. The external implementation always returns 32 bytes;
the Lean wrapper still checks that invariant before constructing `Bytes 32`. -/
@[extern "lean_g1_sha256"]
opaque hashArray : ByteArray → ByteArray

/-- Fast executable SHA-256. A malformed native response maps to the fixed
all-zero value instead of invoking a second, slow implementation. -/
@[inline] def hash (input : ByteArray) : Bytes 32 :=
  let digest := hashArray input
  if h : digest.size = 32 then
    ⟨digest.data, h⟩
  else
    Bytes.zero 32

end SHA256

namespace HMACSHA256

/-- Raw native HMAC-SHA256. The protected executable uses a 32-byte key, while
the native boundary accepts a `ByteArray` so malformed calls can fail closed. -/
@[extern "lean_g1_hmac_sha256"]
opaque hashArray : ByteArray → ByteArray → ByteArray

/-- Protected HMAC-SHA256 wrapper with a checked 32-byte result. -/
@[inline] def hash (key : Bytes 32) (input : ByteArray) : Bytes 32 :=
  let digest := hashArray key.toByteArray input
  if h : digest.size = 32 then
    ⟨digest.data, h⟩
  else
    Bytes.zero 32

end HMACSHA256

end GarblingPrize.Protected
