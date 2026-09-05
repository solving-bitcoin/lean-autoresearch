import Blake3Prize.Protected.ROM

namespace Blake3Prize.Protected

/-- Reviewed proof profiles are part of the protected contract. Adding one
requires specifying its game and assumptions here, never accepting a
submission-provided proposition as its own security assumption. -/
inductive SecurityProfile where
  | classicalBoundedQueryROM
  deriving Repr, DecidableEq

def SecurityRequirement (profile : SecurityProfile) (s : Scheme) : Prop :=
  match profile with
  | .classicalBoundedQueryROM => ROM.Secrecy s

/-- Acceptance is independent of circuits, gate costs, and garbling methods. -/
structure ValidCandidate (s : Scheme) (maxBytes : Nat) (profile : SecurityProfile) : Prop where
  correct : Correct s
  codec : CodecLaws s
  artifact_bound : ArtifactBound s maxBytes
  secret : SecurityRequirement profile s

abbrev RankedClaim := ValidCandidate

/-- The runner executes this very scheme; the proof covers its serialized
transport, its declared universal bound, and its reviewed security profile. -/
structure CertifiedScheme where
  scheme : Scheme
  maxBytes : Nat
  profile : SecurityProfile
  validClaimed : ValidCandidate scheme maxBytes profile

end Blake3Prize.Protected
