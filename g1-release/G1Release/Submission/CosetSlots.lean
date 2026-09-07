import G1Release.Submission.CosetSampler
import G1Release.Submission.OracleAddress

namespace G1Release.Submission.CosetSlots
open SecretRelease G1Release.Protected
abbrev Slot := CosetSampler.TableSlot

def tableWire (kind : Fin 8) (row : Fin 254) : Fin 512 :=
  if kind.val = 4 ∨ kind.val = 5 then ⟨256+row.val,by omega⟩ else ⟨row.val,by omega⟩

def bitsFor (kind : Fin 8) (input : Input) : Fin 254 → Bool :=
  CosetHintMap.inputFor kind (Scheme.xBits input) (Scheme.yBits input)

def inputBits (input : Input) (i : Fin 512) : Bool := (inputCodec.encode input)[i.val]
def selected (keys : Fin 512 → Pair) (input : Input) : Fin 512 → Label :=
  fun i => (keys i).get (inputBits input i)

theorem inputBits_tableWire (input : Input) (kind : Fin 8) (row : Fin 254) :
    inputBits input (tableWire kind row) = bitsFor kind input row := by
  unfold tableWire bitsFor CosetHintMap.inputFor
  split
  · exact Scheme.encodeInput_bit_y input row
  · exact Scheme.encodeInput_bit_x input row

def purpose (slot : Slot) : Nat := CosetHintMap.purpose slot.1.val slot.2.1
def wire (slot : Slot) : Fin 512 := tableWire slot.2.1 slot.2.2
def bit (input : Input) (slot : Slot) : Bool := bitsFor slot.2.1 input slot.2.2

def address (keys : Fin 512 → Pair) (slot : Slot) (branch : Bool) : List (Fin 256) :=
  OracleAddress.query ((keys (wire slot)).get branch) (purpose slot) slot.2.2.val

theorem purpose_lt (slot : Slot) : purpose slot < 65536 := by
  simp only [purpose, CosetHintMap.purpose]
  omega

theorem slot_eq {a b : Slot} (hp : purpose a = purpose b) (hr : a.2.2 = b.2.2) : a = b := by
  simp only [purpose, CosetHintMap.purpose] at hp
  exact Prod.ext (Fin.ext (by omega)) (Prod.ext (Fin.ext (by omega)) hr)

theorem address_injective (keys : Fin 512 → Pair) {a b : Slot} {x y : Bool}
    (h : address keys a x = address keys b y) : a = b ∧ x = y := by
  have ha := OracleAddress.query_injective (purpose_lt a) (purpose_lt b)
    (by omega : a.2.2.val < 65536) (by omega : b.2.2.val < 65536) h
  have hs := slot_eq ha.2.1 (Fin.ext ha.2.2)
  refine ⟨hs, ?_⟩
  subst b
  by_contra hxy
  have hlabels := ha.1
  cases x <;> cases y <;> simp_all [BoundaryFacts.get_false, BoundaryFacts.get_true,
    (keys (wire a)).property, (keys (wire a)).property.symm]

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

end G1Release.Submission.CosetSlots
