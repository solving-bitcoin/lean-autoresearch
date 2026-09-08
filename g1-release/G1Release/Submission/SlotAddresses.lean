import G1Release.Submission.BoundaryFacts
import G1Release.Submission.IdealView
import G1Release.Submission.OracleAddress

namespace G1Release.Submission.SlotAddresses
open SecretRelease G1Release.Protected IdealView Randomized

def purpose (slot : Slot) : Nat := ProjectiveMap.purpose slot.1.val slot.2.1
def wire (slot : Slot) : Fin 512 := tableWire slot.2.1 slot.2.2
def bit (input : Input) (slot : Slot) : Bool := bitsFor slot.2.1 input slot.2.2

def address (keys : Fin 512 → Pair) (slot : Slot) (branch : Bool) : List (Fin 256) :=
  OracleAddress.query ((keys (wire slot)).get branch) (purpose slot) slot.2.2.val

theorem kind_index_lt (kind : ProjectiveMap.TableKind) : kind.index < 11 := by
  cases kind <;> decide

theorem purpose_lt (slot : Slot) : purpose slot < 65536 := by
  have hk := kind_index_lt slot.2.1
  simp only [purpose, ProjectiveMap.purpose]
  omega

theorem kind_index_injective : Function.Injective ProjectiveMap.TableKind.index := by
  intro a b h
  cases a <;> cases b <;> simp only [ProjectiveMap.TableKind.index] at h ⊢ <;> omega

theorem slot_eq {a b : Slot} (hp : purpose a = purpose b) (hr : a.2.2 = b.2.2) : a = b := by
  have ha := kind_index_lt a.2.1
  have hb := kind_index_lt b.2.1
  simp only [purpose, ProjectiveMap.purpose] at hp
  have hi : a.1 = b.1 := Fin.ext (by omega)
  have hk : a.2.1 = b.2.1 := kind_index_injective (by
    have := congrArg Fin.val hi
    omega)
  exact Prod.ext hi (Prod.ext hk hr)

/-- Purpose and row identify the input wire before looking at the label. -/
theorem address_injective (keys : Fin 512 → Pair) {a b : Slot} {x y : Bool}
    (h : address keys a x = address keys b y) : a = b ∧ x = y := by
  have ha := OracleAddress.query_injective (purpose_lt a) (purpose_lt b)
    (by omega : a.2.2.val < 65536) (by omega : b.2.2.val < 65536) h
  have hs := slot_eq ha.2.1 (Fin.ext ha.2.2)
  refine ⟨hs, ?_⟩
  subst b
  by_contra hxy
  have hlabels := ha.1
  cases x <;> cases y <;> simp_all [BoundaryFacts.get_false, BoundaryFacts.get_true, (keys (wire a)).property,
    (keys (wire a)).property.symm]

def inactive (keys : Fin 512 → Pair) (input : Input) (slot : Slot) : List (Fin 256) :=
  address keys slot (!(bit input slot))

def active (keys : Fin 512 → Pair) (input : Input) (slot : Slot) : List (Fin 256) :=
  address keys slot (bit input slot)

theorem inactive_injective (keys : Fin 512 → Pair) (input : Input) :
    Function.Injective (inactive keys input) := by
  intro a b h
  exact (address_injective keys h).1

theorem active_not_inactive (keys : Fin 512 → Pair) (input : Input) (slot : Slot) :
    ¬∃ other, inactive keys input other = active keys input slot := by
  rintro ⟨other,h⟩
  rcases address_injective keys h with ⟨rfl,hn⟩
  simp only [Bool.not_eq_self] at hn

end G1Release.Submission.SlotAddresses
