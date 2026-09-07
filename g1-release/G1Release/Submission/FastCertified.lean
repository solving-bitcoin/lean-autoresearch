import G1Release.Submission.ROMSecurity
import G1Release.Submission.FastSampler
import G1Release.Submission.FastPad

namespace G1Release.Submission.FastCertified
open SecretRelease G1Release.Protected Randomized

def garble (hash : Hash) (coins : SecretRelease.Bytes coinBytes) (hidden : Hidden)
    (keys : challenge.inputs.Keys) (_ : challenge.outputs.Keys) : Scheme.Artifact :=
  FastPad.garble hash hidden (FastSampler.sample coins hidden) keys

theorem garble_eq : garble = executableScheme.garble := by
  funext hash coins hidden keys outputs
  dsimp only [garble]
  exact (congrArg (fun random : Randomness hidden => FastPad.garble hash hidden random keys)
    (FastSampler.sample_eq coins hidden)).trans
      ((FastPad.garble_eq hash hidden (sample coins hidden) keys).trans
        (FastGarble.garble_eq hash hidden (sample coins hidden) keys))

def scheme : SecretRelease.Scheme challenge :=
  { executableScheme with garble := garble }

theorem scheme_eq : scheme = executableScheme := by
  have h := congrArg (fun g => ({ executableScheme with garble := g } : SecretRelease.Scheme challenge)) garble_eq
  exact h

def certificate : SecretRelease.Certificate scheme Scheme.claimedBytes := by
  rw [scheme_eq]
  exact ROMSecurity.certificate

end G1Release.Submission.FastCertified
