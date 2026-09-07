import G1Release.Submission.CosetHintMap

namespace G1Release.Submission.CosetFamilyArtifact

open GarblingPrize.Protected

/-- A concrete vector prevents the compiler from eta-expanding the garbler
into a per-map/per-table sampler. The function view below preserves the
mathematical family and its exact serialized bytes. -/
structure Artifact (count : Nat) where
  storage : Vector CosetHintMap.Artifact count

def Artifact.maps (artifact : Artifact count) : Fin count → CosetHintMap.Artifact :=
  artifact.storage.get

def Artifact.ofMaps (maps : Fin count → CosetHintMap.Artifact) : Artifact count :=
  ⟨Vector.ofFn maps⟩

@[simp] theorem Artifact.maps_ofMaps (maps : Fin count → CosetHintMap.Artifact) :
    (Artifact.ofMaps maps).maps = maps := by
  funext index
  simp only [Artifact.maps, Artifact.ofMaps, Vector.get_ofFn]

@[ext] theorem Artifact.ext (left right : Artifact count) (h : left.maps = right.maps) :
    left = right := by
  cases left with
  | mk left =>
    cases right with
    | mk right =>
      congr 1
      apply Vector.ext
      intro index hindex
      exact congrFun h ⟨index, hindex⟩

@[simp] theorem Artifact.ofMaps_maps (artifact : Artifact count) :
    Artifact.ofMaps artifact.maps = artifact :=
  Artifact.ext _ _ (Artifact.maps_ofMaps artifact.maps)

def byteCount (count : Nat) : Nat :=
  count * CosetHintMap.byteCount

set_option maxRecDepth 4096 in
private def mapCodec : FixedCodec CosetHintMap.Artifact
    CosetHintMap.byteCount where
  encode := fun map =>
    ⟨(CosetHintMap.encode map).data, CosetHintMap.encode_size map⟩
  decode := fun bytes => CosetHintMap.decode bytes.toByteArray
  decode_encode := CosetHintMap.decode_encode
  encode_decode := by
    intro bytes map h
    apply Bytes.toByteArray_injective
    exact CosetHintMap.encode_decode h

def encode (artifact : Artifact count) : ByteArray :=
  FixedCodec.encodeFin mapCodec count artifact.maps

@[simp] theorem encode_size (artifact : Artifact count) :
    (encode artifact).size = byteCount count := by
  exact FixedCodec.encodeFin_size mapCodec artifact.maps

def decodeCore (count : Nat) (input : ByteArray) :
    Except WireDecodeError (Artifact count) := do
  let maps ← FixedCodec.decodeFin mapCodec count input
  pure (Artifact.ofMaps maps)

def decode (count : Nat) (input : ByteArray) :
    Except WireDecodeError (Artifact count) :=
  decodeCore count input

@[simp] theorem decodeCore_encode (artifact : Artifact count) :
    decodeCore count (encode artifact) = .ok artifact := by
  unfold decodeCore encode
  rw [FixedCodec.decodeFin_encode]
  exact congrArg Except.ok (Artifact.ofMaps_maps artifact)

@[simp] theorem decode_encode (artifact : Artifact count) :
    decode count (encode artifact) = .ok artifact :=
  decodeCore_encode artifact

theorem encode_decode {bytes : ByteArray} {artifact : Artifact count}
    (h : decode count bytes = .ok artifact) : encode artifact = bytes := by
  unfold decode decodeCore at h
  cases hmaps : FixedCodec.decodeFin mapCodec count bytes with
  | error error => simp [hmaps, Except.bind, bind] at h
  | ok maps =>
      have hartifact : Artifact.ofMaps maps = artifact := by
        simp only [hmaps, Except.bind, bind] at h
        exact Except.ok.inj h
      rw [← hartifact]
      simpa only [encode, Artifact.maps_ofMaps] using
        FixedCodec.encodeFin_decode mapCodec hmaps

theorem ninetyOne_byteCount : byteCount 91 = 5940480 := by decide

end G1Release.Submission.CosetFamilyArtifact
