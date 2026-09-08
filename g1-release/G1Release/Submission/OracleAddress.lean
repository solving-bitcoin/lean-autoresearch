import G1Release.Submission.AffineTable

/-! Honest oracle addresses encode a 32-byte label and two fixed-width
integers. Distinct table/row purposes remain distinct even when different
input wires happen to have equal labels. -/
namespace G1Release.Submission.OracleAddress
open AffineTable

def address (label : Label) (purpose row : Nat) : ByteArray :=
  ByteArray.mk (label.toArray ++ natLE8 purpose ++ natLE8 row)

theorem pad_eq (hash : Hash) (label : Label) (purpose row : Nat) :
    pad hash label purpose row = hash (address label purpose row) := rfl

theorem natLE8_injective_below {a b : Nat} (ha : a < 65536) (hb : b < 65536)
    (h : natLE8 a = natLE8 b) : a = b := by
  have h0 := congrArg (fun v : Array UInt8 => v[0]?.map UInt8.toNat) h
  have h1 := congrArg (fun v : Array UInt8 => v[1]?.map UInt8.toNat) h
  simp [natLE8, Nat.shiftRight_eq_div_pow] at h0 h1
  omega

theorem address_injective {left right : Label} {p q i j : Nat}
    (hp : p < 65536) (hq : q < 65536) (hi : i < 65536) (hj : j < 65536)
    (h : address left p i = address right q j) :
    left = right ∧ p = q ∧ i = j := by
  have hdata := congrArg ByteArray.data h
  have hsplit := Array.append_inj hdata (by simp [natLE8])
  have hprefix := Array.append_inj hsplit.1 (by simp)
  refine ⟨?_, natLE8_injective_below hp hq hprefix.2,
    natLE8_injective_below hi hj hsplit.2⟩
  exact Vector.toArray_inj.mp hprefix.1

def query (label : Label) (purpose row : Nat) : List (Fin 256) :=
  (address label purpose row).data.toList.map UInt8.toFin

theorem query_injective {left right : Label} {p q i j : Nat}
    (hp : p < 65536) (hq : q < 65536) (hi : i < 65536) (hj : j < 65536)
    (h : query left p i = query right q j) :
    left = right ∧ p = q ∧ i = j := by
  apply address_injective hp hq hi hj
  apply ByteArray.ext
  apply Array.toList_inj.mp
  exact (List.map_inj_right (fun _ _ heq => UInt8.toFin_inj.mp heq)).mp h

end G1Release.Submission.OracleAddress
