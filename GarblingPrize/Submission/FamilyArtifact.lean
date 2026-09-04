import GarblingPrize.Submission.ProjectiveMap

namespace GarblingPrize.Submission.FamilyArtifact

open GarblingPrize.Protected

@[ext] structure Artifact (count : Nat) where
  maps : Fin count → ProjectiveMap.Artifact

def byteCount (count : Nat) : Nat := count * ProjectiveMap.mapByteCount

set_option maxRecDepth 4096 in
private def mapCodec : FixedCodec ProjectiveMap.Artifact
    ProjectiveMap.mapByteCount where
  encode := fun map => ⟨(ProjectiveMap.encode map).data, ProjectiveMap.encode_size map⟩
  decode := fun bytes => ProjectiveMap.decode bytes.toByteArray
  decode_encode := ProjectiveMap.decode_encode
  encode_decode := by
    intro bytes map h
    apply Bytes.toByteArray_injective
    exact ProjectiveMap.encode_decode h

def encode (artifact : Artifact count) : ByteArray :=
  FixedCodec.encodeFin mapCodec count artifact.maps

/-- Parallel executable encoder. Each map is independent and already has a
fixed-width canonical encoding; results are joined in the same index order. -/
def encodeParallel (artifact : Artifact count) : ByteArray :=
  FixedCodec.encodeFinParallel mapCodec count artifact.maps

@[simp] theorem encodeParallel_eq (artifact : Artifact count) :
    encodeParallel artifact = encode artifact := by
  simp [encodeParallel, encode]

@[simp] theorem encode_size (artifact : Artifact count) :
    (encode artifact).size = byteCount count := by
  exact FixedCodec.encodeFin_size mapCodec artifact.maps

def decodeCore (count : Nat) (input : ByteArray) :
    Except WireDecodeError (Artifact count) := do
  let maps ← FixedCodec.decodeFin mapCodec count input
  pure ⟨maps⟩

def decode (count : Nat) (input : ByteArray) :
    Except WireDecodeError (Artifact count) :=
  decodeCore count input

@[simp] theorem decodeCore_encode (artifact : Artifact count) :
    decodeCore count (encode artifact) = .ok artifact := by
  unfold decodeCore encode
  rw [FixedCodec.decodeFin_encode]
  rfl

@[simp] theorem decode_encode (artifact : Artifact count) :
    decode count (encode artifact) = .ok artifact := by
  exact decodeCore_encode artifact

theorem encode_decode {bytes : ByteArray} {artifact : Artifact count}
    (h : decode count bytes = .ok artifact) : encode artifact = bytes := by
  unfold decode decodeCore at h
  cases hmaps : FixedCodec.decodeFin mapCodec count bytes with
  | error error => simp [hmaps, Except.bind, bind] at h
  | ok maps =>
      have hartifact : ({ maps := maps } : Artifact count) = artifact := by
        simp only [hmaps, Except.bind, bind] at h
        change Except.ok ({ maps := maps } : Artifact count) =
          Except.ok artifact at h
        exact Except.ok.inj h
      rw [← hartifact]
      exact FixedCodec.encodeFin_decode mapCodec hmaps

theorem threadedMask_byteCount : byteCount 161 = 28564459 := by decide

end GarblingPrize.Submission.FamilyArtifact
