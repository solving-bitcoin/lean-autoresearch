import Blake3Prize.Submission.RomGate

/-! Domain separation includes the protocol tag, table role, wire/output
index, and semantic row. Address injectivity does not require different
wires' labels to be different. The 16-bit bound covers the planned circuit. -/
namespace Blake3Prize.Submission.RomAddress
open SecretRelease

def natLE8 (n : Nat) : Array UInt8 :=
  Array.ofFn fun i : Fin 8 => UInt8.ofNat (n >>> (8*i.val))

def header (role index : Nat) : ByteArray :=
  ⟨#[66,51,52,1] ++ natLE8 role ++ natLE8 index⟩

theorem natLE8_injective {a b : Nat} (ha : a < 65536) (hb : b < 65536)
    (h : natLE8 a = natLE8 b) : a = b := by
  have h0 := congrArg (fun v : Array UInt8 => v[0]?.map UInt8.toNat) h
  have h1 := congrArg (fun v : Array UInt8 => v[1]?.map UInt8.toNat) h
  simp [natLE8,Nat.shiftRight_eq_div_pow] at h0 h1
  omega

@[simp] theorem header_size (role index : Nat) : (header role index).size = 20 := by
  simp [header,natLE8,ByteArray.size]

theorem header_injective {p q i j : Nat}
    (hp : p < 65536) (hq : q < 65536) (hi : i < 65536) (hj : j < 65536)
    (h : header p i = header q j) : p = q ∧ i = j := by
  have hd := congrArg ByteArray.data h
  have hs := Array.append_inj hd (by simp [natLE8])
  have hr := Array.append_inj hs.1 (by simp)
  exact ⟨natLE8_injective hp hq hr.2,natLE8_injective hi hj hs.2⟩

def rowRole (row : RomGate.Row) : Nat := (if row.1 then 2 else 0)+(if row.2 then 1 else 0)

theorem rowRole_lt (row : RomGate.Row) : rowRole row < 4 := by
  rcases row with ⟨a,b⟩
  cases a <;> cases b <;> decide

theorem rowRole_injective : Function.Injective rowRole := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  cases a <;> cases b <;> cases c <;> cases d <;> first | rfl | contradiction

def gateContext (wire : Nat) (row : RomGate.Row) : ByteArray := header (rowRole row) wire
def outputContext (index : Nat) (bit : Bool) : ByteArray := header (if bit then 5 else 4) index

theorem gate_query_injective {p q : RomGate.Row} {i j : Nat} {a b c d : Label}
    (hi : i < 65536) (hj : j < 65536)
    (h : RomGate.query (gateContext i p) a b = RomGate.query (gateContext j q) c d) :
    p = q ∧ i = j ∧ a = c ∧ b = d := by
  have hd := congrArg ByteArray.data h
  simp only [RomGate.query,ByteArray.data_append,RomBytes.encode] at hd
  have hs := Array.append_inj hd (by simp [gateContext,header,natLE8])
  have ht := Array.append_inj hs.1 (by simp [gateContext,header,natLE8])
  have hh := header_injective (by have := rowRole_lt p; omega)
    (by have := rowRole_lt q; omega) hi hj (ByteArray.ext ht.1)
  exact ⟨rowRole_injective hh.1,hh.2,Vector.toArray_inj.mp ht.2,Vector.toArray_inj.mp hs.2⟩

theorem output_query_injective {p q : Bool} {i j : Nat} {a b : Label}
    (hi : i < 65536) (hj : j < 65536)
    (h : outputContext i p ++ RomBytes.encode a = outputContext j q ++ RomBytes.encode b) :
    p = q ∧ i = j ∧ a = b := by
  have hd := congrArg ByteArray.data h
  simp only [ByteArray.data_append,RomBytes.encode] at hd
  have hs := Array.append_inj hd (by simp [outputContext,header,natLE8])
  have hh := header_injective (by split <;> decide) (by split <;> decide)
    hi hj (ByteArray.ext hs.1)
  refine ⟨?_,hh.2,Vector.toArray_inj.mp hs.2⟩
  cases p <;> cases q <;> simp_all

end Blake3Prize.Submission.RomAddress
