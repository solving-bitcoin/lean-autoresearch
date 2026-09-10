import G1Release.Submission.CosetRandomness
import G1Release.Submission.CosetFamilyArtifact
import G1Release.Submission.RuntimeG1GLV
import G1Release.Submission.SchemeCorrect

/-! Finite-label ROM implementation of the eight-table coset construction.
The input keys are the challenge's 32-byte Lamport labels. Pad families are
computed by querying the supplied hash at (label, map/table purpose, row).
No ideal-pad or modulus-oracle interface is part of this scheme. -/
namespace G1Release.Submission.CosetScheme
set_option maxRecDepth 4096
open SecretRelease G1Release.Protected G1Release.Math
open GLVDigits CosetCoordinates FourAffineQuotient
open Scheme (runtimeOfGroup toPoint_runtimeOfGroup inputG1 xBits yBits)

abbrev Randomness := CosetRandomness.Randomness
abbrev Artifact := CosetFamilyArtifact.Artifact 91
abbrev Coins := Fin 91 → CosetHintMap.Coins
abbrev Keys := Fin 512 → Pair
abbrev Word := BN254.Fq
abbrev Point := RuntimeG1.Point

/-- Each table/row domain is unique; the branch is selected by its secret label. -/
def pads (hash : Hash) (labels : Fin 254 → Label) : Fin 254 → HintAffineTable.PadFamily :=
  fun row purpose => AffineTable.pad hash (labels row) purpose row.val

def xPads (hash : Hash) (keys : Keys) : Fin 254 → Bool → HintAffineTable.PadFamily :=
  fun row branch purpose => pads hash (fun i => Scheme.xPairs keys i branch) row purpose

def yPads (hash : Hash) (keys : Keys) : Fin 254 → Bool → HintAffineTable.PadFamily :=
  fun row branch purpose => pads hash (fun i => Scheme.yPairs keys i branch) row purpose

def mapBase (hidden : Private) (random : Randomness hidden) (index : Fin 91) : Base K :=
  CosetGLV.mapBase (offsetAt random.offsets index) (digitAt hidden index)

def mapParams (hidden : Private) (random : Randomness hidden)
    (index : Fin 91) (kind : CosetHintMap.TableKind) : AffineTable.Params :=
  CosetHintMap.params (mapBase hidden random index) (random.states index) kind

def garble (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (coins : Coins) (keys : Keys) : Artifact :=
  CosetFamilyArtifact.Artifact.ofMaps fun index =>
    CosetHintMap.garble index.val (xPads hash keys) (yPads hash keys)
      (mapBase hidden random index) (random.states index) (coins index)

@[simp] theorem garble_maps (hash : Hash) (hidden : Private) (random : Randomness hidden)
    (coins : Coins) (keys : Keys) :
    (garble hash hidden random coins keys).maps = fun index =>
      CosetHintMap.garble index.val (xPads hash keys) (yPads hash keys)
        (mapBase hidden random index) (random.states index) (coins index) :=
  CosetFamilyArtifact.Artifact.maps_ofMaps _

def finish (x : Word) (opened : Option (Opened K)) : Option Point := do
  let values ← opened
  CosetCoordinates.decode (reconstruct values (C x))

def evaluateMap (hash : Hash) (index : Fin 91) (map : CosetHintMap.Artifact)
    (input : Input) (active : ByteArray) : Option Point :=
  finish (input.val.1.val : Word) (CosetHintMap.evaluate index.val map (xBits input) (yBits input)
    (pads hash (Scheme.evalXLabels active)) (pads hash (Scheme.evalYLabels active)))

def evaluateMaps (hash : Hash) (artifact : Artifact) (input : Input)
    (active : ByteArray) : List (Fin 91) → Option (List Point)
  | [] => some []
  | index :: indices => do
      let point ← evaluateMap hash index (artifact.maps index) input active
      let rest ← evaluateMaps hash artifact input active indices
      pure (point :: rest)

def evaluate (hash : Hash) (artifact : Artifact) (input : Input)
    (active : ByteArray) : Option ByteArray := do
  if active.size != 16384 then none else do
    let points ← evaluateMaps hash artifact input active (List.finRange 91)
    match RuntimeG1.recomposeAlpha points with
    | .error _ => none
    | .ok result => some (encodeOutput (RuntimeG1.toOutput result))

def encode : Artifact → ByteArray := CosetFamilyArtifact.encode

def decode (bytes : ByteArray) : Option Artifact :=
  (CosetFamilyArtifact.decode 91 bytes).toOption

theorem decode_encode (artifact : Artifact) : decode (encode artifact) = some artifact := by
  unfold decode encode
  rw [CosetFamilyArtifact.decode_encode]
  rfl

theorem encode_decode (bytes : ByteArray) (artifact : Artifact)
    (h : decode bytes = some artifact) : encode artifact = bytes := by
  unfold decode at h
  cases hd : CosetFamilyArtifact.decode 91 bytes with
  | error error =>
    rw [hd] at h
    change none = some artifact at h
    cases h
  | ok decoded =>
    rw [hd] at h
    have he : decoded = artifact := Option.some.inj h
    subst decoded
    exact CosetFamilyArtifact.encode_decode hd

def claimedBytes : Nat := 5940480

theorem encode_size (artifact : Artifact) : (encode artifact).size = claimedBytes := by
  exact CosetFamilyArtifact.encode_size artifact

theorem claimedBytes_lt_sixMB : claimedBytes < 6000000 := by decide

/-- All randomness comes from a fixed finite byte tape. Security of its
sampling law is a separate theorem, never an assumption in this interface. -/
def scheme (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Private) → Randomness hidden × Coins) :
    SecretRelease.Scheme challenge where
  Artifact := Artifact
  randomnessBytes := n
  garble := fun hash coins hidden keys _ =>
    let random := sample coins hidden
    garble hash hidden random.1 random.2 keys
  encode := encode
  decode := decode
  evaluate := evaluate

@[simp] theorem scheme_encode (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Private) → Randomness hidden × Coins) :
    (scheme n sample).encode = encode := rfl

@[simp] theorem scheme_decode (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Private) → Randomness hidden × Coins) :
    (scheme n sample).decode = decode := rfl

@[simp] theorem scheme_garble (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Private) → Randomness hidden × Coins)
    (hash : Hash) (coins : SecretRelease.Bytes n) (hidden : Private)
    (keys : challenge.inputs.Keys) (outputs : challenge.outputs.Keys) :
    (scheme n sample).garble hash coins hidden keys outputs =
      garble hash hidden (sample coins hidden).1 (sample coins hidden).2 keys := rfl

@[simp] theorem scheme_evaluate (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Private) → Randomness hidden × Coins)
    (hash : Hash) (artifact : Artifact) (input : Input) (active : ByteArray) :
    (scheme n sample).evaluate hash artifact input active = evaluate hash artifact input active := rfl

theorem artifactBound (n : Nat)
    (sample : SecretRelease.Bytes n → (hidden : Private) → Randomness hidden × Coins) :
    ArtifactBound (scheme n sample) claimedBytes := by
  intro hash coins hidden keys outputs
  exact le_of_eq (encode_size _)

end G1Release.Submission.CosetScheme
