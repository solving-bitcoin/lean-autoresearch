import Blake3Prize.Protected.Core
import Clean.Specs.SHA256

namespace Blake3Prize.Protected

/-- Executable instantiation of the optional public hash. The ROM certificate
is about an IDEAL random oracle; this definition is not a proof that SHA-256
realizes that model. No native crypto implementation is substituted for Lean. -/
def nativeHash (bytes : ByteArray) : Label :=
  let words := Specs.SHA256.sha256 (bytes.data.toList.map UInt8.toNat)
  Vector.ofFn fun i =>
    UInt8.ofNat ((words[i.val / 4] / 2^(8*(3-i.val%4))) % 256)

end Blake3Prize.Protected
