import Blake3Prize.Protected.Reference
import Mathlib.Tactic.Ring

namespace Blake3Prize.Protected.HalfGate

/-- One coordinate of the 256-bit half-gates equations. Hash outputs are
arbitrary: correctness does not assume pseudorandomness or collision resistance.
The semantic input bits toggle the low selector bits because delta has low bit 1. -/
def select (b : Bool) (x : Bit) : Bit := if b then x else 0

def garblerHalf (ha0 ha1 delta : Bit) (sb0 : Bool) : Bit :=
  ha0 + ha1 + select sb0 delta

def evaluatorHalf (hb0 hb1 a0 : Bit) : Bit := hb0 + hb1 + a0

def outputZero (a0 ha0 hb0 tg te : Bit) (sa0 sb0 : Bool) : Bit :=
  ha0 + select sa0 tg + hb0 + select sb0 (te + a0)

def evaluate (a0 delta ha0 ha1 hb0 hb1 tg te : Bit) (sa0 sb0 x y : Bool) : Bit :=
  (if x then ha1 else ha0) + select (sa0 ^^ x) tg +
    (if y then hb1 else hb0) + select (sb0 ^^ y) (te + a0 + select x delta)

theorem correct (a0 delta ha0 ha1 hb0 hb1 : Bit) (sa0 sb0 x y : Bool) :
    evaluate a0 delta ha0 ha1 hb0 hb1
        (garblerHalf ha0 ha1 delta sb0) (evaluatorHalf hb0 hb1 a0) sa0 sb0 x y =
      outputZero a0 ha0 hb0 (garblerHalf ha0 ha1 delta sb0)
        (evaluatorHalf hb0 hb1 a0) sa0 sb0 + select (x && y) delta := by
  cases sa0 <;> cases sb0 <;> cases x <;> cases y <;>
    simp [evaluate, outputZero, garblerHalf, evaluatorHalf, select] <;>
    ring_nf <;> simp [show (2 : Bit) = 0 from rfl]

/-- The characteristic-two carry used by zk.golf is a Boolean majority. -/
theorem carry_truth (a b c : Bool) :
    ((a ^^ c) && (b ^^ c)) ^^ c = ((a && b) || (a && c) || (b && c)) := by
  cases a <;> cases b <;> cases c <;> rfl

end Blake3Prize.Protected.HalfGate
