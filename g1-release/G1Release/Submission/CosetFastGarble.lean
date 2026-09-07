import G1Release.Submission.FastHintRow
import G1Release.Submission.CosetFastSampler

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace G1Release.Submission.CosetFastGarble
open SecretRelease G1Release.Protected CosetSampler

def fromRandom (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : CosetScheme.Keys) : CosetScheme.Artifact :=
  CosetFamilyArtifact.Artifact.ofMaps fun index =>
    ⟨fun kind => FastHintRow.garble (CosetHintMap.purpose index.val kind)
      (CosetHintMap.inputFor kind (CosetScheme.xPads hash keys) (CosetScheme.yPads hash keys))
      (CosetScheme.mapParams hidden random.1 index kind) (random.2 index kind)⟩

theorem fromRandom_eq (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (keys : CosetScheme.Keys) :
    fromRandom hash hidden random keys = CosetScheme.garble hash hidden random.1 random.2 keys := by
  simp only [fromRandom, CosetScheme.garble, CosetHintMap.garble,
    FastHintRow.garble_eq, CosetScheme.mapParams]

/-- Materialize input pairs once, sample once, and pack each row bytewise. -/
def garble (hash : Hash) (coins : SecretRelease.Bytes coinBytes) (hidden : Private)
    (keys : challenge.inputs.Keys) (_ : challenge.outputs.Keys) : CosetScheme.Artifact :=
  let cached := Vector.ofFn keys
  let random := CosetFastSampler.sample coins hidden
  fromRandom hash hidden random cached.get

theorem garble_eq (hash : Hash) (coins : SecretRelease.Bytes coinBytes) (hidden : Private)
    (keys : challenge.inputs.Keys) (outputs : challenge.outputs.Keys) :
    garble hash coins hidden keys outputs = CosetFastSampler.scheme.garble hash coins hidden keys outputs := by
  have hk : (Vector.ofFn keys).get = keys := by
    funext i
    exact Vector.get_ofFn keys i
  simp only [garble, hk, CosetFastSampler.scheme, CosetScheme.scheme_garble]
  exact fromRandom_eq hash hidden (CosetFastSampler.sample coins hidden) keys

def scheme : SecretRelease.Scheme challenge :=
  { CosetFastSampler.scheme with garble := garble }

theorem scheme_eq : scheme = CosetFastSampler.scheme := by
  have hg : garble = CosetFastSampler.scheme.garble := by
    funext hash coins hidden keys outputs
    exact garble_eq hash coins hidden keys outputs
  simp only [scheme, hg]

end G1Release.Submission.CosetFastGarble
