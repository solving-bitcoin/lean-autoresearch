import G1Release.Submission.CosetFastSampler
import G1Release.Submission.DutyFreeScheme

/-! Keep the proved coset sampler as the first independent component of the
coin tape. A separate 65,536-byte suffix supplies 128 × 16 independent
256-bit bridge keys. Unused legacy row coins are private and are not part
of the serialized artifact. The tape split is a bijection, not a PRG. -/
namespace G1Release.Submission.DutyFreeSampler
open SecretRelease G1Release.Protected
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def split (n m : Nat) (tape : Bytes (n+m)) : Bytes n × Bytes m :=
  (Vector.ofFn fun i => tape.get ⟨i.val, by omega⟩,
   Vector.ofFn fun i => tape.get ⟨n+i.val, by have := i.isLt; omega⟩)

def join {n m : Nat} (parts : Bytes n × Bytes m) : Bytes (n+m) :=
  Vector.ofFn fun i => if h : i.val < n then parts.1.get ⟨i.val,h⟩
    else parts.2.get ⟨i.val-n, by have := i.isLt; omega⟩

def splitEquiv (n m : Nat) : Bytes (n+m) ≃ Bytes n × Bytes m where
  toFun := split n m
  invFun := join
  left_inv tape := by
    ext i hi
    simp only [join, split, Vector.getElem_ofFn, Vector.get_ofFn]
    split
    · rfl
    · have he : n + (i-n) = i := by omega
      simp only [he, Vector.get_eq_getElem]
  right_inv parts := by
    apply Prod.ext
    · ext i hi
      simp only [split, join, Vector.getElem_ofFn, Vector.get_ofFn, dif_pos hi,
        Vector.get_eq_getElem]
    · ext i hi
      have hn : ¬n+i < n := by omega
      simp only [split, join, Vector.getElem_ofFn, Vector.get_ofFn, dif_neg hn,
        Nat.add_sub_cancel_left, Vector.get_eq_getElem]

def hotEquiv : Bytes 65536 ≃ DutyFreeProgram.HotKeys :=
  (FiniteProbability.blockEquiv 128 512).trans
    (Equiv.piCongrRight fun _ => FiniteProbability.blockEquiv 16 32)

/-- Concrete storage prevents function-result eta expansion from rebuilding
the complete key cache on every lookup. -/
def hotStorage (coins : Bytes 65536) : Vector (Vector Label 16) 128 :=
  Vector.ofFn fun i => Vector.ofFn fun j => hotEquiv coins i j

def hotKeys (coins : Bytes 65536) : DutyFreeProgram.HotKeys :=
  fun i j => ((hotStorage coins).get i).get j

theorem hotKeys_eq (coins : Bytes 65536) : hotKeys coins = hotEquiv coins := by
  funext i j
  simp only [hotKeys, hotStorage, Vector.get_ofFn]

def coinBytes : Nat := CosetSampler.coinBytes + 65536

def sample (coins : Bytes coinBytes) (hidden : Private) :
    DutyFreeProgram.Randomness hidden × DutyFreeProgram.HotKeys :=
  let parts := split CosetSampler.coinBytes 65536 coins
  let cached := hotStorage parts.2
  ((CosetFastSampler.sample parts.1 hidden).1, fun i j => (cached.get i).get j)

def scheme : SecretRelease.Scheme challenge := schemeWith coinBytes sample
theorem correct : Correct scheme := correctWith coinBytes sample
theorem artifactBound : ArtifactBound scheme 1776384 := artifactBoundWith coinBytes sample

/-- Executable development entry; ranking still requires the two ROM games. -/
def entry : SecretRelease.Candidate challenge where
  scheme := scheme
  maxBytes := 1776384
  certificate := none

end G1Release.Submission.DutyFreeSampler
