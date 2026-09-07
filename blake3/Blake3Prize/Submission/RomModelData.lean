import Blake3Prize.Submission.RomKeyMaterial
import Blake3Prize.Submission.RomQueryEncoding
import Blake3Prize.Submission.RomSelectedKeys

namespace Blake3Prize.Submission.RomModelData
open SecretRelease Blake3Prize.Protected RomKeyMaterial RomMixedKeys RomMixedGuessing
open RomQueryEncoding

noncomputable def node (wire : Nat) : RomGraph.Node := (RomGraph.lookup RomBlake3.program wire).getD ⟨false,0,0⟩
noncomputable def left (w : Nat) : KeyIndex := wire (node w).left
noncomputable def right (w : Nat) : KeyIndex := wire (node w).right
noncomputable def outputWire (i : Fin 256) : Nat := (RomGraph.outputs RomBlake3.program).get i
noncomputable def outputSource (i : Fin 256) : KeyIndex := wire (outputWire i)

noncomputable def selected (input : Input) (keys : KeySet) : Active 768 61186 :=
  (RomMixedKeys.split (externalBits input) (internalBits input) keys).1

theorem active_selected (input : Input) (keys : KeySet) (i : KeyIndex) :
    activeLabel (selected input keys) i = key keys i (keyBit input i) :=
  RomSelectedKeys.selected_key (externalBits input) (internalBits input) keys i

noncomputable def isActive (input : Input) : Slot → Bool
  | .inl value => decide (value.2 = (keyBit input (left value.1.val),keyBit input (right value.1.val)))
  | .inr value => decide (value.2 = keyBit input (outputSource value.1))

noncomputable def witness (keys : KeySet) : Slot → Witness
  | .inl value => .inl (value,(key keys (left value.1.val) value.2.1,
      key keys (right value.1.val) value.2.2))
  | .inr value => .inr (value,key keys (outputSource value.1) value.2)

noncomputable def publicWitness (active : Active 768 61186) : Slot → Witness
  | .inl value => .inl (value,(activeLabel active (left value.1.val),
      activeLabel active (right value.1.val)))
  | .inr value => .inr (value,activeLabel active (outputSource value.1))

noncomputable def address (keys : KeySet) (slot : Slot) : RomTableModel.Address := encoded (witness keys slot)
noncomputable def publicAddress (active : Active 768 61186) (slot : Slot) : RomTableModel.Address :=
  encoded (publicWitness active slot)

noncomputable def gatePayloadBit (input : Input) (w : Nat) (row : RomGate.Row) : Bool :=
  match RomGraph.lookup RomBlake3.program w with
  | some gate => gate.function row.1 row.2
  | none => keyBit input (wire w)

noncomputable def payload (input : Input) (keys : KeySet) : Slot → Label
  | .inl value => key keys (wire value.1.val) (gatePayloadBit input value.1.val value.2)
  | .inr value => key keys (out value.1) value.2

noncomputable def publicPayload (active : Active 768 61186) : Slot → Label
  | .inl value => activeLabel active (wire value.1.val)
  | .inr value => activeLabel active (out value.1)

theorem address_injective (keys : KeySet) : Function.Injective (address keys) := by
  intro a b h
  have he := congrArg RomQueryEncoding.slot (encoded_injective h)
  have ha : RomQueryEncoding.slot (witness keys a) = a := by cases a <;> rfl
  have hb : RomQueryEncoding.slot (witness keys b) = b := by cases b <;> rfl
  exact ha.symm.trans (he.trans hb)

theorem address_active (input : Input) (keys : KeySet) (slot : Slot)
    (h : isActive input slot = true) :
    address keys slot = publicAddress (selected input keys) slot := by
  cases slot with
  | inl value =>
    have he : value.2 = (keyBit input (left value.1.val),keyBit input (right value.1.val)) :=
      of_decide_eq_true h
    simp only [address,publicAddress,witness,publicWitness,active_selected]
    rw [he]
  | inr value =>
    have he : value.2 = keyBit input (outputSource value.1) := of_decide_eq_true h
    simp only [address,publicAddress,witness,publicWitness,active_selected,he]

theorem gate_consistent (input : Input) (w : Nat) (gate : RomGraph.Node)
    (hg : RomGraph.lookup RomBlake3.program w = some gate) :
    keyBit input (wire w) = gate.function (keyBit input (wire gate.left))
      (keyBit input (wire gate.right)) := by
  have hb := RomGraph.lookup_bounds RomBlake3.program w gate hg
  rw [RomBlake3.program_nodes] at hb
  rw [wire_bit input w (by omega),wire_bit input gate.left (by omega),
    wire_bit input gate.right (by omega)]
  exact RomGraph.lookup_consistent RomBlake3.program _
    (RomGraph.values_consistent RomBlake3.program (RomInput.known input)) w gate hg

theorem output_consistent (input : Input) (i : Fin 256) :
    keyBit input (outputSource i) = keyBit input (out i) := by
  have hb := RomGraph.outputs_bound RomBlake3.program i
  rw [RomBlake3.program_nodes] at hb
  rw [outputSource,wire_bit input (outputWire i) (by exact hb),out_bit]
  exact (RomGraph.outputs_values RomBlake3.program (RomInput.known input) i).trans
    (congrArg (fun v => v.get i) (RomBlake3.program_correct input))

theorem payload_active (input : Input) (keys : KeySet) (slot : Slot)
    (h : isActive input slot = true) :
    payload input keys slot = publicPayload (selected input keys) slot := by
  cases slot with
  | inl value =>
    have he : value.2 = (keyBit input (left value.1.val),keyBit input (right value.1.val)) :=
      of_decide_eq_true h
    simp only [payload,publicPayload,active_selected]
    apply congrArg (key keys (wire value.1.val))
    rw [he]
    cases hg : RomGraph.lookup RomBlake3.program value.1.val with
    | none => simp only [gatePayloadBit,hg]
    | some gate =>
      simp only [gatePayloadBit,hg,left,right,node,Option.getD_some]
      exact (gate_consistent input value.1.val gate hg).symm
  | inr value =>
    have he : value.2 = keyBit input (outputSource value.1) := of_decide_eq_true h
    simp only [payload,publicPayload,active_selected,he,output_consistent]

noncomputable def guessWitness (input : Input) : Witness → KeyIndex × Label
  | .inl value =>
      if value.1.2.1 = keyBit input (left value.1.1.val) then (right value.1.1.val,value.2.2)
      else (left value.1.1.val,value.2.1)
  | .inr value => (outputSource value.1.1,value.2)

noncomputable def guess (input : Input) (query : RomTableModel.Address) : Option (KeyIndex × Label) :=
  (RomQueryEncoding.decode query).map (guessWitness input)

theorem bool_opposite {a b : Bool} (h : a ≠ b) : a = !b := by
  cases a <;> cases b <;> simp_all

theorem guess_inactive (input : Input) (keys : KeySet) (slot : Slot)
    (h : isActive input slot = false) :
    ∃ i, guess input (address keys slot) = some (i,key keys i (!(keyBit input i))) := by
  rw [guess,address,decode_encoded,Option.map_some]
  cases slot with
  | inl value =>
    have he : value.2 ≠ (keyBit input (left value.1.val),keyBit input (right value.1.val)) :=
      of_decide_eq_false h
    by_cases hl : value.2.1 = keyBit input (left value.1.val)
    · have hr : value.2.2 ≠ keyBit input (right value.1.val) := by
        intro hr
        exact he (Prod.ext hl hr)
      refine ⟨right value.1.val,?_⟩
      simp only [witness,guessWitness,if_pos hl,bool_opposite hr]
    · refine ⟨left value.1.val,?_⟩
      dsimp only [witness,guessWitness]
      rw [if_neg hl,bool_opposite hl]
  | inr value =>
    have he : value.2 ≠ keyBit input (outputSource value.1) := of_decide_eq_false h
    refine ⟨outputSource value.1,?_⟩
    simp only [witness,guessWitness,bool_opposite he]

noncomputable def model (input : Input) : RomTableModel.Model 768 61186 Slot where
  externalBits := externalBits input
  internalBits := internalBits input
  isActive := isActive input
  address := address
  payload := payload input
  publicAddress := publicAddress
  publicPayload := publicPayload
  address_injective := address_injective
  address_active := address_active input
  payload_active := payload_active input
  guess := guess input
  guess_inactive := guess_inactive input

end Blake3Prize.Submission.RomModelData
