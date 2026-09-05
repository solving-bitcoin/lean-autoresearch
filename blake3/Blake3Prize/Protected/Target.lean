import Blake3Prize.Protected.Morphism
import Blake3Prize.Protected.Lowering
import Blake3Prize.Protected.HalfGate
import Blake3Prize.Protected.Codec

namespace Blake3Prize.Protected

abbrev Candidate := Vector BitExpr 256

def Correct (candidate : Candidate) : Prop :=
  ∀ input : Input, candidate.map (BitExpr.eval input) = reference input

/-- A circuit-optimization certificate under the frozen half-gates backend.
Cryptographic security relies on its documented random-oracle assumptions;
it is not an exact information-theoretic theorem about 32-byte keys. -/
structure ValidCandidate (candidate : Candidate) (maxBytes : Nat) : Prop where
  correct : Correct candidate
  artifact_bound : artifactBytes (Lowering.compile candidate) ≤ maxBytes

abbrev RankedClaim := ValidCandidate

/-- Production-shaped API: garbling has no message argument; evaluation has
neither plaintext bits, label pairs, secret seeds, nor an output decoder. -/
structure GarblingAPI where
  garble : (Nat → Label) → InputLabelPairs → OutputLabelPairs → ByteArray
  evaluate : ByteArray → ActiveInputLabels → Option ActiveOutputLabels

def LabelCorrect (api : GarblingAPI) : Prop :=
  ∀ coins inputPairs outputPairs input,
    DistinctPairs inputPairs → DistinctPairs outputPairs →
    api.evaluate (api.garble coins inputPairs outputPairs) (activeInput inputPairs input) =
      some (activeOutput outputPairs (reference input))

end Blake3Prize.Protected
