import WotsLamport.Submission.Threshold

/-! Executable weighted-Shamir research candidate. No certificate is claimed.
All source and proofs in this project still require actual Lean compilation.
Field arithmetic, interpolation, exact bytes and joint ROM security obligations
are listed in PROOF_STATUS.md; tests do not discharge them. -/
namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

def prime : Nat := 65537
def coefficientCount : Nat := 512 * 16 * 1023
def randomnessBytes : Nat := 32 + coefficientCount * 32
def bodyBytes : Nat := 32 + 512*32 + 256*(1984+1982)*48
def artifactBytes : Nat := 2144 + bodyBytes

def readLE (b : ByteArray) (start length : Nat) : Nat :=
  (List.range length).foldr (fun j acc => b[start+j]!.toNat + 256*acc) 0
def writeLE (length n : Nat) : ByteArray :=
  ⟨(List.range length).toArray.map fun j => UInt8.ofNat (n / 256^j)⟩
def xorBytes (a b : ByteArray) : ByteArray :=
  ⟨(List.range a.size).toArray.map fun j => a[j]! ^^^ b[j]!⟩
def fadd (a b : Nat) : Nat := (a+b) % prime
def fmul (a b : Nat) : Nat := (a*b) % prime
def fsub (a b : Nat) : Nat := (a+prime-b) % prime
/-- Fixed 16 squarings for inversion in F_65537. -/
def inverse (a : Nat) : Nat :=
  ((List.range 16).foldl (fun (s : Nat × Nat) _ => (fmul s.1 s.2, fmul s.2 s.2)) (1,a)).1

def holds (i : Fin 256) (value : Bool) (digit : Nat) : Bool := digitBit i digit == value
def targetChain (i : Fin 256) : Fin 67 := ⟨(bitChain i).val, by have := (bitChain i).isLt; omega⟩

/-- Every listed slot has its own distinct nonzero evaluation coordinate. Public
endpoints k=D_j are never used as mask keys. Duplicate chain slots are distinct
shares with distinct mask domains, not duplicate interpolation coordinates. -/
def slots (i : Fin 256) (value : Bool) : List (Fin 67 × Nat) :=
  (List.finRange 67).flatMap fun j => (List.range (maximum j)).flatMap fun k =>
    let count := if j = targetChain i then
      (multiplicity (weight j) (holds i value) k).toNat else weight j
    List.replicate count (j,k)

def threshold (value : Bool) : Nat := if value then 1023 else 1024
def polynomial (coins : ByteArray) (label : Label) (wire limb : Nat) (value : Bool) : List Nat :=
  let id := 2*wire + if value then 1 else 0
  (List.range (threshold value)).map fun degree =>
    if degree = 0 then readLE ⟨label.toArray⟩ (2*limb) 2 else
      readLE coins (32 + ((id*16+limb)*1023+degree-1)*32) 32 % prime
def evaluatePolynomial (coefficients : List Nat) (x : Nat) : Nat :=
  coefficients.foldr (fun a acc => fadd a (fmul x acc)) 0

def domain (tag : String) (pk nonce : ByteArray) (wire : Nat) (value : Bool) : ByteArray :=
  tag.toUTF8 ++ nonce ++ pk ++ writeLE 2 wire ++ writeLE 1 (if value then 1 else 0)
def mask (h : Hash) (pk nonce : ByteArray) (wire : Nat) (value : Bool)
    (point : Nat) (node : Label) : ByteArray :=
  let maskInput := domain "WOTS-LAMPORT/mask/v1" pk nonce wire value ++ writeLE 2 point ++ ⟨node.toArray⟩
  let first := h (maskInput ++ writeLE 1 0)
  let second := h (maskInput ++ writeLE 1 1)
  ⟨first.toArray⟩ ++ (ByteArray.mk second.toArray).extract 0 16
def commitment (h : Hash) (pk nonce : ByteArray) (wire : Nat) (value : Bool) (label : Label) : Label :=
  h (domain "WOTS-LAMPORT/label/v1" pk nonce wire value ++ ⟨label.toArray⟩)

def concatenate (parts : List ByteArray) : ByteArray :=
  parts.foldl (fun acc part => acc ++ part) ByteArray.empty

def labelTable (h : Hash) (coins pk nonce : ByteArray) (keys : Keys)
    (i : Fin 256) (value : Bool) (label : Label) : ByteArray :=
  let polys := (List.range 16).map fun limb => polynomial coins label i.val limb value
  concatenate ((slots i value).zipIdx.map fun ((j,k), index) =>
    let point := index+1
    let share := concatenate (polys.map fun p => writeLE 3 (evaluatePolynomial p point))
    xorBytes share (mask h pk nonce i.val value point (chain h k (keys j))))

def prepare (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : ByteArray :=
  let nonce := coins.extract 0 32
  let pk := keyCodec.encode (publicKey h keys)
  nonce ++ concatenate ((List.finRange 256).map fun i =>
    (ByteArray.mk (commitment h pk nonce i.val false ((labels i).get false)).toArray) ++
    (ByteArray.mk (commitment h pk nonce i.val true ((labels i).get true)).toArray)) ++
  concatenate ((List.finRange 256).map fun i =>
    labelTable h coins pk nonce keys i false ((labels i).get false) ++
    labelTable h coins pk nonce keys i true ((labels i).get true))

def interpolationFactors (shares : List (Nat × List Nat)) (a : Nat) (initial : Nat × Nat) : Nat × Nat :=
  shares.foldl (fun (nd : Nat × Nat) b =>
    if a = b.1 then nd else (fmul nd.1 (fsub 0 b.1), fmul nd.2 (fsub a b.1))) initial

def interpolationWeight (shares : List (Nat × List Nat)) (a : Nat) : Nat :=
  let nd := interpolationFactors shares a (1,1)
  fmul nd.1 (inverse nd.2)

def interpolate (shares : List (Nat × List Nat)) : List Nat :=
  let weighted := shares.map fun a => (interpolationWeight shares a.1, a.2)
  (List.range 16).map fun limb =>
    weighted.foldl (fun acc a => fadd acc (fmul a.1 a.2[limb]!)) 0

def expand (h : Hash) (pk : PublicKey) (body : ByteArray) (m : Message) (sig : Signature) : Option ByteArray := do
  if body.size != bodyBytes then none else do
    let publicBytes := keyCodec.encode pk
    let nonce := body.extract 0 32
    let mut result := ByteArray.empty
    for i in List.finRange 256 do
      let value := (outputCodec.encode m)[i.val]
      let offset := 32 + 512*32 + (i.val*(1984+1982) + if value then 1984 else 0)*48
      let mut shares : List (Nat × List Nat) := []
      for ((j,k), index) in (slots i value).zipIdx do
        if encodeWord m j ≤ k then
          let node := chain h (k - encodeWord m j) (sig j)
          let plain := xorBytes (body.extract (offset+index*48) (offset+(index+1)*48))
            (mask h publicBytes nonce i.val value (index+1) node)
          let fields := (List.range 16).map fun limb => readLE plain (3*limb) 3
          if fields.any (fun x => decide (x ≥ prime)) then failure
          shares := shares ++ [(index+1,fields)]
      if shares.length != threshold value then failure
      let recovered := interpolate shares
      if recovered.any (fun x => decide (x ≥ 65536)) then failure
      let bytes := recovered.foldl (fun acc x => acc ++ writeLE 2 x) ByteArray.empty
      let label ← (Codec.byteVector 32).bytes.decode bytes
      let expected := body.extract (32+(2*i.val+(if value then 1 else 0))*32)
        (32+(2*i.val+(if value then 1 else 0)+1)*32)
      if (ByteArray.mk (commitment h publicBytes nonce i.val value label).toArray) != expected then failure
      result := result ++ bytes
    return result

def construction : Construction := ⟨randomnessBytes, prepare, expand⟩

end WotsLamport.Submission
