import Blake3Prize.Submission.RomRounds
import Blake3Prize.Submission.RomInput

set_option maxRecDepth 4096

namespace Blake3Prize.Submission.RomBlake3
open Blake3Prize.Protected RomProgram RomCounts HalfGates

def wordBits (words : Vector (BitVec 32) 8) : Vector Bool 256 :=
  Vector.ofFn fun i => (words.get ⟨i.val/32,by omega⟩).getLsbD (i.val%32)

def finish : RomProgram.Program 1025 256 := RomParallel.xorWords
  (Vector.ofFn fun i : Fin 256 =>
    (RomRegisters.word ⟨i.val/32,by omega⟩).get ⟨i.val%32,by omega⟩)
  (Vector.ofFn fun i : Fin 256 =>
    (RomRegisters.word ⟨i.val/32+8,by omega⟩).get ⟨i.val%32,by omega⟩)

theorem finish_correct (v m : Vector (BitVec 32) 16) :
    finish.eval (RomRegisters.encoding (v ++ m)) =
      wordBits (WordProgram.finish RomWordSemantics.ops v) := by
  rw [finish,RomParallel.eval_xorWords]
  apply Vector.ext
  intro i hi
  have hl := congrArg (fun bits : Vector Bool 32 => bits.get ⟨i%32,by omega⟩)
    (RomRegisters.encoding_word (v ++ m) ⟨i/32,by omega⟩)
  have hr := congrArg (fun bits : Vector Bool 32 => bits.get ⟨i%32,by omega⟩)
    (RomRegisters.encoding_word (v ++ m) ⟨i/32+8,by omega⟩)
  simp only [Vector.get_map] at hl hr
  simp only [Vector.getElem_ofFn,Vector.get_ofFn]
  rw [hl,hr,RomVector.append_get_left v m ⟨i/32,by omega⟩,
    RomVector.append_get_left v m ⟨i/32+8,by omega⟩]
  simp [wordBits,WordProgram.finish,RomWordSemantics.ops,RomArithmetic.bits,
    RomArithmetic.slice,Vector.get_eq_getElem,
    BitVec.getLsbD_eq_getElem (by omega : i%32 < 32)]

theorem reference_encoded (input : Input) (i : Fin 256) :
    ((SecretRelease.Codec.byteVector 32).encode (reference input)).get i =
      ((referenceWords (inputWords input)).get ⟨i.val/32,by omega⟩).testBit (i.val%32) :=
  ReferenceEncoding.reference_encoded input i

theorem digest_bits (input : Input) :
    wordBits (RomWordSemantics.digest input) = (SecretRelease.Codec.byteVector 32).encode (reference input) := by
  apply Vector.ext
  intro i hi
  have hw := congrArg (fun words : Vector Nat 8 => words.get ⟨i/32,by omega⟩)
    (RomWordSemantics.digest_nat input)
  simp only [Vector.get_map] at hw
  change (wordBits (RomWordSemantics.digest input)).get ⟨i,hi⟩ =
    ((SecretRelease.Codec.byteVector 32).encode (reference input)).get ⟨i,hi⟩
  have he := reference_encoded input ⟨i,hi⟩
  exact (show (wordBits (RomWordSemantics.digest input)).get ⟨i,hi⟩ =
      ((referenceWords (inputWords input)).get ⟨i/32,by omega⟩).testBit (i%32) from
    (by simp only [wordBits,Vector.get_ofFn]; exact congrArg (fun n => n.testBit (i%32)) hw)).trans he.symm

@[irreducible] def program : RomProgram.Program 514 256 :=
  RomInput.prepare.comp (RomRounds.rounds.program.comp finish)

theorem program_correct (input : Input) :
    program.eval (RomInput.known input) = (SecretRelease.Codec.byteVector 32).encode (reference input) := by
  rw [program,eval_comp,RomInput.prepare_correct,eval_comp,RomRounds.rounds.correct,
    RomRounds.run_rounds,finish_correct]
  exact digest_bits input

theorem finish_nodes : nodes finish = 256 := nodes_xorWords _ _

theorem program_nodes : nodes program = 61184 := by
  rw [program,nodes_comp,nodes_comp,RomRounds.rounds.count,finish_nodes,RomRounds.rounds_cost]
  rfl

end Blake3Prize.Submission.RomBlake3
