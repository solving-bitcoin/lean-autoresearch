import WotsLamport.Submission.CachedImplementation

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected

/-- Evaluate sixteen independent limbs together using scalar machine accumulators.
Complete byte-for-byte correspondence is proved separately in LaneSharing. -/
structure HornerLanes where
  c0 : UInt32
  c1 : UInt32
  c2 : UInt32
  c3 : UInt32
  c4 : UInt32
  c5 : UInt32
  c6 : UInt32
  c7 : UInt32
  c8 : UInt32
  c9 : UInt32
  c10 : UInt32
  c11 : UInt32
  c12 : UInt32
  c13 : UInt32
  c14 : UInt32
  c15 : UInt32

def HornerLanes.get (row : HornerLanes) (i : Fin 16) : UInt32 :=
  match i.val with
  | 0 => row.c0
  | 1 => row.c1
  | 2 => row.c2
  | 3 => row.c3
  | 4 => row.c4
  | 5 => row.c5
  | 6 => row.c6
  | 7 => row.c7
  | 8 => row.c8
  | 9 => row.c9
  | 10 => row.c10
  | 11 => row.c11
  | 12 => row.c12
  | 13 => row.c13
  | 14 => row.c14
  | _ => row.c15

def HornerLanes.ofFn (f : Fin 16 → UInt32) : HornerLanes :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11, f 12, f 13, f 14, f 15⟩

def lanesHorner (x : UInt32) : List HornerLanes → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → UInt32 → HornerLanes
  | [], s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15 => ⟨s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15⟩
  | row :: rest, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15 =>
      lanesHorner x rest
        (reduceMachineField (row.c0 + x * s0))
        (reduceMachineField (row.c1 + x * s1))
        (reduceMachineField (row.c2 + x * s2))
        (reduceMachineField (row.c3 + x * s3))
        (reduceMachineField (row.c4 + x * s4))
        (reduceMachineField (row.c5 + x * s5))
        (reduceMachineField (row.c6 + x * s6))
        (reduceMachineField (row.c7 + x * s7))
        (reduceMachineField (row.c8 + x * s8))
        (reduceMachineField (row.c9 + x * s9))
        (reduceMachineField (row.c10 + x * s10))
        (reduceMachineField (row.c11 + x * s11))
        (reduceMachineField (row.c12 + x * s12))
        (reduceMachineField (row.c13 + x * s13))
        (reduceMachineField (row.c14 + x * s14))
        (reduceMachineField (row.c15 + x * s15))

def laneCoefficients (coins : ByteArray) (label : Label) (wire : Nat) (value : Bool) :
    List HornerLanes :=
  let id := 2*wire + if value then 1 else 0
  (List.range (threshold value)).reverse.map fun degree =>
    HornerLanes.ofFn fun limb => UInt32.ofNat
      ((if degree = 0 then readLE ⟨label.toArray⟩ (2*limb.val) 2 else
        readMachineField coins (32+((id*16+limb.val)*1023+degree-1)*32) 32) % prime)

def laneEvaluate (coefficients : List HornerLanes) (x : Nat) : HornerLanes :=
  lanesHorner (UInt32.ofNat x) coefficients 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0

def laneShare (rows : List HornerLanes) (x : Nat) : ByteArray :=
  let result := laneEvaluate rows x
  concatenate ((List.range 16).map fun limb =>
    writeLE 3 (result.get ⟨limb % 16, Nat.mod_lt _ (by decide)⟩).toNat)

def laneLabelTable (h : Hash) (coins pk nonce : ByteArray) (cache : PreparedChainCache)
    (i : Fin 256) (value : Bool) (label : Label) : ByteArray :=
  let rows := laneCoefficients coins label i.val value
  concatenate ((slots i value).zipIdx.map fun ((j,k), index) =>
    let point := index+1
    xorBytes (laneShare rows point) (mask h pk nonce i.val value point (cachedChainNode cache j k)))

def lanePrepare (h : Hash) (coins : ByteArray) (keys : Keys)
    (labels : Fin 256 → Pair) : ByteArray :=
  let nonce := coins.extract 0 32
  let pk := keyCodec.encode (publicKey h keys)
  let cache := prepareChainCache h keys
  nonce ++ concatenate ((List.finRange 256).map fun i =>
    (ByteArray.mk (commitment h pk nonce i.val false ((labels i).get false)).toArray) ++
    (ByteArray.mk (commitment h pk nonce i.val true ((labels i).get true)).toArray)) ++
  concatenate ((List.finRange 256).map fun i =>
    laneLabelTable h coins pk nonce cache i false ((labels i).get false) ++
    laneLabelTable h coins pk nonce cache i true ((labels i).get true))

def laneConstruction : Construction := ⟨randomnessBytes, lanePrepare, expand⟩


end WotsLamport.Submission
