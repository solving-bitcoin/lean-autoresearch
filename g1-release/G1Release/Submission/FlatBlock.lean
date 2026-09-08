import G1Release.Submission.WordChunks

set_option exponentiation.threshold 1024
set_option maxHeartbeats 500000
set_option maxRecDepth 4096

namespace G1Release.Submission.FlatBlock
open SecretRelease

/-- The caller computes the block offset once. Keeping this boundary stops
specialization from recomputing a coordinate's tag and stride for every byte. -/
@[irreducible, noinline] def toFin (bytes : Bytes width) (offset : Nat) (h : offset+64 ≤ width) : Fin (2^512) :=
  WordChunks.toFin (n := 8) (fun i => bytes.get ⟨offset+i.val,by omega⟩)

theorem toFin_eq (bytes : Bytes (count*64)) (slot : Fin count) :
    toFin bytes (slot.val*64) (by omega) =
      FiniteProbability.bytesFinEquiv 64 (FiniteProbability.blockEquiv count 64 bytes slot) := by
  let byte := fun i : Fin 64 => bytes.get ⟨slot.val*64+i.val,by omega⟩
  have hb : Vector.ofFn byte = FiniteProbability.blockEquiv count 64 bytes slot := by
    apply Vector.ext
    intro i hi
    simp only [byte,FiniteProbability.blockEquiv,Equiv.coe_fn_mk,Vector.getElem_ofFn]
    apply congrArg bytes.get
    apply Fin.ext
    change slot.val*64+i = 64*slot.val+i
    omega
  have he : toFin bytes (slot.val*64) (by omega) = FlatArithmetic.toFin (n := 8) byte := by
    unfold toFin
    exact WordChunks.toFin_eq _
  exact he.trans ((FlatArithmetic.toFin_eq (n := 8) byte).trans
    (congrArg (FiniteProbability.bytesFinEquiv 64) hb))

end G1Release.Submission.FlatBlock
