import WotsLamport.Submission.MachineImplementation

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

abbrev PreparedChainCache := Vector (Vector Label 16) 67

def prepareChainCache (h : Hash) (keys : Keys) : PreparedChainCache :=
  Vector.ofFn fun j => Vector.ofFn fun k => chain h k.val (keys j)

def cachedChainNode (cache : PreparedChainCache) (j : Fin 67) (k : Nat) : Label :=
  cache[j.val][k]!

def cachedLabelTable (h : Hash) (coins pk nonce : ByteArray) (cache : PreparedChainCache)
    (i : Fin 256) (value : Bool) (label : Label) : ByteArray :=
  let polys := (List.range 16).map fun limb =>
    machineCoefficients (machinePolynomial coins label i.val limb value)
  concatenate ((slots i value).zipIdx.map fun ((j,k), index) =>
    let point := index+1
    let share := concatenate (polys.map fun p => writeLE 3 (evaluateMachinePolynomial p point))
    xorBytes share (mask h pk nonce i.val value point (cachedChainNode cache j k)))

def cachedPrepare (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : ByteArray :=
  let nonce := coins.extract 0 32
  let pk := keyCodec.encode (publicKey h keys)
  let cache := prepareChainCache h keys
  nonce ++ concatenate ((List.finRange 256).map fun i =>
    (ByteArray.mk (commitment h pk nonce i.val false ((labels i).get false)).toArray) ++
    (ByteArray.mk (commitment h pk nonce i.val true ((labels i).get true)).toArray)) ++
  concatenate ((List.finRange 256).map fun i =>
    cachedLabelTable h coins pk nonce cache i false ((labels i).get false) ++
    cachedLabelTable h coins pk nonce cache i true ((labels i).get true))

def cachedConstruction : Construction := ⟨randomnessBytes, cachedPrepare, expand⟩

end WotsLamport.Submission
