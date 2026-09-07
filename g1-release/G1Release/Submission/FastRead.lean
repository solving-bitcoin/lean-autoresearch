import G1Release.Submission.WordChunks

namespace G1Release.Submission.FastRead
open SecretRelease

@[inline] def read (bytes : Bytes (n*8)) : Nat := WordChunks.read bytes.get n (Nat.le_refl n)

theorem read_eq (bytes : Bytes (n*8)) :
    read bytes = ByteArithmetic.read bytes (n*8) (Nat.le_refl (n*8)) := by
  unfold read
  rw [WordChunks.read_eq,FlatArithmetic.chunks_ofFn,PackedArithmetic.read_eq]
  have hv : Vector.ofFn bytes.get = bytes := by
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn,Vector.get_eq_getElem]
  rw [hv]

end G1Release.Submission.FastRead
