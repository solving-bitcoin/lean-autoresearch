import Blake3Prize.Submission.RomAddress
import Blake3Prize.Submission.RomTableModel

namespace Blake3Prize.Submission.RomQueryEncoding
open SecretRelease

abbrev Slot := (Fin 65536 × RomGate.Row) ⊕ (Fin 256 × Bool)
abbrev Witness := ((Fin 65536 × RomGate.Row) × (Label × Label)) ⊕ ((Fin 256 × Bool) × Label)

def byteAddress (bytes : ByteArray) : RomTableModel.Address := bytes.data.toList.map UInt8.toFin

theorem byteAddress_injective : Function.Injective byteAddress := by
  intro a b h
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact (List.map_inj_right (fun _ _ heq => UInt8.toFin_inj.mp heq)).mp h

def bytes : Witness → ByteArray
  | .inl value => RomGate.query (RomAddress.gateContext value.1.1.val value.1.2)
      value.2.1 value.2.2
  | .inr value => RomAddress.outputContext value.1.1.val value.1.2 ++ RomBytes.encode value.2

def encoded (value : Witness) : RomTableModel.Address := byteAddress (bytes value)

theorem encoded_injective : Function.Injective encoded := by
  intro a b h
  have hb := byteAddress_injective h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have he := RomAddress.gate_query_injective a.1.1.isLt b.1.1.isLt hb
      exact congrArg Sum.inl
        (Prod.ext (Prod.ext (Fin.ext he.2.1) he.1) (Prod.ext he.2.2.1 he.2.2.2))
    | inr b =>
      have hs := congrArg ByteArray.size hb
      simp [bytes,RomGate.query,RomAddress.gateContext,RomAddress.outputContext] at hs
  | inr a =>
    cases b with
    | inl b =>
      have hs := congrArg ByteArray.size hb
      simp [bytes,RomGate.query,RomAddress.gateContext,RomAddress.outputContext] at hs
    | inr b =>
      have he := RomAddress.output_query_injective (by omega : a.1.1.val < 65536)
        (by omega : b.1.1.val < 65536) hb
      exact congrArg Sum.inr (Prod.ext (Prod.ext (Fin.ext he.2.1) he.1) he.2.2)

def slot : Witness → Slot
  | .inl value => .inl value.1
  | .inr value => .inr value.1

/-- Proof-only parsing of adversarial queries, independent of key material. -/
noncomputable def decode (query : RomTableModel.Address) : Option Witness := by
  classical
  exact if h : ∃ value, encoded value = query then some (Classical.choose h) else none

theorem decode_encoded (value : Witness) : decode (encoded value) = some value := by
  classical
  have he : ∃ v, encoded v = encoded value := ⟨value,rfl⟩
  have hc := encoded_injective (Classical.choose_spec he)
  simp [decode,he,hc]

end Blake3Prize.Submission.RomQueryEncoding
