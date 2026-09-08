import Blake3Prize.Submission.RomModelData
import Blake3Prize.Submission.RomScheme
import Blake3Prize.Submission.RomTableSecurity
import Blake3Prize.Submission.RomViewEquality

namespace Blake3Prize.Submission.RomRendering
open SecretRelease Blake3Prize.Protected RomKeyMaterial RomMixedKeys RomMixedGuessing
open RomQueryEncoding

/-- An owned unfolding lemma avoids generating equations in the protected namespace. -/
theorem hash_apply (oracle : ROM.Oracle) (query : ByteArray) :
    ROM.hash oracle query = oracle (byteAddress query) := rfl

noncomputable def gateTables (ciphertexts : Slot → Label) (w : Nat) (row : RomGate.Row) : Label :=
  if h : w < 65536 then ciphertexts (.inl (⟨w,h⟩,row)) else RomBytes.zero 32

noncomputable def circuit (ciphertexts : Slot → Label) : RomExecution.Artifact 256 :=
  RomGraph.render RomBlake3.program (gateTables ciphertexts)
    (fun i b => ciphertexts (.inr (i,b)))

noncomputable def view (input : Input) (active : Active 768 61186) (ciphertexts : Slot → Label) : View challenge :=
  ⟨input,pack (activeLabel active (wire 512) :: activeLabel active (wire 513) ::
      RomCells.flatten (circuit ciphertexts)),
    pack ((List.finRange 512).map fun i => activeLabel active (.inl ⟨i.val,by omega⟩)),
    pack ((List.finRange 256).map fun i => activeLabel active (out i))⟩

theorem tables_eq (input : Input) (keys : KeySet) (oracle : ROM.Oracle) :
    RomScheme.tables (ROM.hash oracle) keys =
      circuit (RomTableModel.ciphertexts (RomModelData.model input) keys oracle) := by
  rw [RomScheme.tables_spec]
  let ciphertexts := RomTableModel.ciphertexts (RomModelData.model input) keys oracle
  refine (RomGraph.garble_render RomBlake3.program (ROM.hash oracle)
    RomAddress.gateContext (fun i => RomAddress.outputContext i.val)
    (wireKeys keys) (outKeys keys) (gateTables ciphertexts) ?_).trans ?_
  · intro w node hn
    have hb := RomGraph.lookup_bounds RomBlake3.program w node hn
    rw [RomBlake3.program_nodes] at hb
    funext row
    simp only [gateTables,dif_pos (by omega : w < 65536),ciphertexts,
      RomTableModel.ciphertexts,RomModelData.model,RomModelData.payload,
      RomModelData.gatePayloadBit,hn,RomModelData.address,encoded,
      RomModelData.witness,RomModelData.left,RomModelData.right,RomModelData.node,
      Option.getD_some,bytes,byteAddress,RomGate.table,RomGate.query,hash_apply,
      wireKeys]
  · change RomGraph.render RomBlake3.program (gateTables ciphertexts) _ =
      RomGraph.render RomBlake3.program (gateTables ciphertexts) _
    apply congrArg (RomGraph.render RomBlake3.program (gateTables ciphertexts))
    funext i b
    simp only [RomGate.translate,ciphertexts,RomTableModel.ciphertexts,
      RomModelData.model,RomModelData.payload,RomModelData.address,
      RomModelData.witness,encoded,bytes,byteAddress,hash_apply,
      RomModelData.outputSource,RomModelData.outputWire,wireKeys,outKeys]

theorem constant_false (input : Input) : keyBit input (wire 512) = false := by
  rw [wire_bit input 512 (by decide)]
  exact (RomGraph.values_prefix RomBlake3.program (RomInput.known input)
    ⟨512,by decide⟩).trans (RomInput.known_zero input)

theorem constant_true (input : Input) : keyBit input (wire 513) = true := by
  rw [wire_bit input 513 (by decide)]
  exact (RomGraph.values_prefix RomBlake3.program (RomInput.known input)
    ⟨513,by decide⟩).trans (RomInput.known_one input)

theorem artifact_eq (input : Input) (keys : KeySet) (oracle : ROM.Oracle) :
    pack (RomScheme.cells (ROM.hash oracle) keys) =
      (view input (RomModelData.selected input keys)
        (RomTableModel.ciphertexts (RomModelData.model input) keys oracle)).artifact := by
  simp only [view,RomModelData.active_selected,constant_false,constant_true,
    RomScheme.cells,wireKeys,tables_eq input keys oracle]

theorem selected_input (input : Input) (coins : Bytes 3915904)
    (inputs : Fin 512 → Pair) (outputs : Fin 256 → Pair) (i : Fin 512) :
    activeLabel (RomModelData.selected input (assemble coins inputs outputs))
      (.inl ⟨i.val,by omega⟩) = (inputs i).get (inputBit input i) := by
  rw [RomModelData.active_selected]
  change ((externalEquiv (inputs,outputs)) ⟨i.val,by omega⟩).get
    (externalBits input ⟨i.val,by omega⟩) = _
  simp only [externalEquiv,Equiv.coe_fn_mk,externalBits,dif_pos i.isLt]

theorem selected_output (input : Input) (coins : Bytes 3915904)
    (inputs : Fin 512 → Pair) (outputs : Fin 256 → Pair) (i : Fin 256) :
    activeLabel (RomModelData.selected input (assemble coins inputs outputs)) (out i) =
      (outputs i).get (((SecretRelease.Codec.byteVector 32).encode (reference input)).get i) := by
  rw [RomModelData.active_selected,out_bit]
  exact assembled_output coins inputs outputs i _

theorem actual_view (input : Input) (p : Unit) (sample : ROM.Sample RomScheme.scheme) :
    ROM.view RomScheme.scheme p input sample =
      RomTableSecurity.realView (RomModelData.model input) (view input)
        (assemble sample.2.2.1 sample.1 sample.2.1,sample.2.2.2) := by
  refine RomViewEquality.ext rfl ?_ ?_ ?_
  · exact (RomScheme.garble_bytes (ROM.hash sample.2.2.2) sample.2.2.1 p sample.1 sample.2.1).trans
      (artifact_eq input (assemble sample.2.2.1 sample.1 sample.2.1) sample.2.2.2)
  · refine (RomScheme.input_reveal (ROM.hash sample.2.2.2) sample.1 input).trans ?_
    apply congrArg pack
    apply List.map_congr_left
    intro i _
    exact (selected_input input sample.2.2.1 sample.1 sample.2.1 i).symm
  · refine (RomScheme.output_reveal (ROM.hash sample.2.2.2) sample.2.1 input).trans ?_
    apply congrArg pack
    apply List.map_congr_left
    intro i _
    exact (selected_output input sample.2.2.1 sample.1 sample.2.1 i).symm

end Blake3Prize.Submission.RomRendering
