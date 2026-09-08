import Blake3Prize.Submission.RomKeyBytes
import Blake3Prize.Submission.RomBlake3
import Blake3Prize.Submission.RomGraph

namespace Blake3Prize.Submission.RomKeyMaterial
open SecretRelease RomMixedKeys RomMixedGuessing Blake3Prize.Protected

def externalBits (input : Input) (i : Fin 768) : Bool :=
  if h : i.val < 512 then inputBit input ⟨i.val,h⟩
  else ((Codec.byteVector 32).encode (reference input)).get (⟨i.val-512,by omega⟩ : Fin 256)

theorem external_input (input : Input) (i : Fin 512) :
    externalBits input ⟨i.val,by omega⟩ = inputBit input i := by
  simp only [externalBits,dif_pos i.isLt]

def internalBits (input : Input) (i : Fin 61186) : Bool :=
  RomGraph.values RomBlake3.program (RomInput.known input) (512+i.val)

def keyBit (input : Input) : KeyIndex → Bool := bit (externalBits input) (internalBits input)

theorem input_bit (input : Input) (i : Fin 512) :
    (RomInput.known input).get ⟨i.val,by omega⟩ = inputBit input i := RomInput.known_input input i

theorem wire_bit (input : Input) (n : Nat) (hn : n < 61698) :
    keyBit input (wire n) = RomGraph.values RomBlake3.program (RomInput.known input) n := by
  refine wire_bit_of (externalBits input) (internalBits input)
    (RomGraph.values RomBlake3.program (RomInput.known input)) ?_ (fun _ => rfl) n hn
  intro i
  exact (external_input input i).trans
    ((RomGraph.values_prefix RomBlake3.program (RomInput.known input)
      ⟨i.val,by omega⟩).trans (input_bit input i)).symm

theorem out_bit (input : Input) (i : Fin 256) :
    keyBit input (out i) = ((SecretRelease.Codec.byteVector 32).encode (reference input)).get i := by
  change externalBits input ⟨512+i.val,by omega⟩ = _
  rw [externalBits,dif_neg (by omega : ¬512+i.val < 512)]
  change (((Codec.byteVector 32).encode (reference input)).get (⟨512+i.val-512,by omega⟩ : Fin 256)) =
    (((Codec.byteVector 32).encode (reference input)).get i)
  simp

theorem assembled_input (coins : Bytes 3915904) (inputs : Fin 512 → Pair)
    (outputs : Fin 256 → Pair) (i : Fin 512) (b : Bool) :
    wireKeys (assemble coins inputs outputs) i.val b = (inputs i).get b := by
  simp only [wireKeys,wire,dif_pos i.isLt,key,assemble,externalEquiv,
    Equiv.coe_fn_mk,Sum.elim_inl]

theorem assembled_output (coins : Bytes 3915904) (inputs : Fin 512 → Pair)
    (outputs : Fin 256 → Pair) (i : Fin 256) (b : Bool) :
    outKeys (assemble coins inputs outputs) i b = (outputs i).get b := by
  change ((externalEquiv (inputs,outputs)) ⟨512+i.val,by omega⟩).get b = _
  simp [externalEquiv]

end Blake3Prize.Submission.RomKeyMaterial
