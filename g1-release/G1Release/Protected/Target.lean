import G1Release.Protected.Codecs
import SecretRelease.Profiles

namespace G1Release.Protected
open SecretRelease
open G1Release.Math

/-- Exact BN254 group semantics; A is a valid finite-affine point. -/
def reference (p : Private) (a : Input) : Output :=
  BN254.CanonicalOutput.ofPoint
    (p.1.toPoint + p.2.val • BN254.ofAffine a.val.1 a.val.2 a.property)

/-- Construction-independent, finite-label ROM challenge. The scalar and
point offset are private; the canonical plaintext result is permitted leakage. -/
def challenge : SecretRelease.Challenge where
  Private := Private
  Input := Input
  Output := Output
  privateCodec := privateCodec
  inputCodec := inputCodec
  inputs := Lamport inputCodec
  outputs := Plain encodeOutput
  reference := reference
  Claim := Fin 512 × SecretRelease.Label
  wins := fun _ _ a keys _ guess =>
    guess.2 = (keys guess.1).get (!(inputCodec.encode a)[guess.1.val])
  privateLeakage := some fun p a => encodeOutput (reference p a)
  rom := SecretRelease.Profiles.rom128

abbrev CertifiedScheme := SecretRelease.Certified challenge

end G1Release.Protected
