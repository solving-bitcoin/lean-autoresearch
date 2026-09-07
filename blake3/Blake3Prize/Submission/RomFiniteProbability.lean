import SecretRelease.Encoding
import Mathlib.Probability.UniformOn
import Mathlib.Probability.ProductMeasure

namespace Blake3Prize.Submission.RomFiniteProbability
open SecretRelease MeasureTheory ProbabilityTheory

/-- A finite-space bijection preserves the actual uniform probability law. -/
theorem uniform_equiv {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [Finite α] [Finite β] [Nonempty α] [Nonempty β] (e : α ≃ β) :
    MeasurePreserving e (uniformOn Set.univ) (uniformOn Set.univ) := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  refine ⟨Measurable.of_discrete, ?_⟩
  ext event hevent
  rw [Measure.map_apply Measurable.of_discrete hevent,
    uniformOn_univ, uniformOn_univ,
    Measure.count_apply (hevent.preimage Measurable.of_discrete),
    Measure.count_apply hevent,
    Set.encard_preimage_of_bijective e.bijective, Fintype.card_congr e]

def vectorEquiv (α : Type) (n : Nat) : Vector α n ≃ (Fin n → α) where
  toFun := Vector.get
  invFun := Vector.ofFn
  left_inv v := by ext i hi; simp [Vector.get_eq_getElem]
  right_inv f := by funext i; simp

/-- The shared byte codec is total on all bit strings at byte-aligned widths. -/
def bytesBitsEquiv (n : Nat) : Bytes n ≃ Vector Bool (n*8) where
  toFun := (Codec.byteVector n).encode
  invFun bits := Vector.ofFn fun i => UInt8.ofNat
    (Nat.ofBits fun j : Fin 8 => bits[i.val*8+j.val])
  left_inv bytes := Option.some.inj ((Codec.byteVector n).decode_encode bytes)
  right_inv bits := (Codec.byteVector n).encode_decode bits _ rfl

def bitsFinEquiv (n : Nat) : Vector Bool n ≃ Fin (2^n) where
  toFun bits := ⟨Nat.ofBits bits.get, Nat.ofBits_lt_two_pow _⟩
  invFun value := Vector.ofFn fun i => value.val.testBit i.val
  left_inv bits := by
    ext i hi
    simp [Nat.testBit_ofBits_lt, hi, Vector.get_eq_getElem]
  right_inv value := by
    apply Fin.ext
    change Nat.ofBits (Vector.ofFn fun i : Fin n => value.val.testBit i.val).get = value.val
    rw [show (Vector.ofFn fun i : Fin n => value.val.testBit i.val).get =
        (fun i : Fin n => value.val.testBit i.val) by funext i; simp,
      Nat.ofBits_testBit, Nat.mod_eq_of_lt value.isLt]

def bytesFinEquiv (n : Nat) : Bytes n ≃ Fin (2^(n*8)) :=
  (bytesBitsEquiv n).trans (bitsFinEquiv (n*8))

theorem label_card : Nat.card Label = 2^256 := by
  simpa using Nat.card_congr (bytesFinEquiv 32)

def preimageEquiv {α β : Type*} (e : α ≃ β) (s : Set β) : (e ⁻¹' s) ≃ s where
  toFun x := ⟨e x.val, x.property⟩
  invFun y := ⟨e.symm y.val, by simpa using y.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv y := by apply Subtype.ext; exact e.apply_symm_apply y.val

theorem uniform_real {α : Type*} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    [Finite α] (event : Set α) :
    (uniformOn Set.univ event).toReal = (Nat.card event : ℝ) / Nat.card α := by
  classical
  letI := Fintype.ofFinite α
  rw [uniformOn_univ, Measure.count_apply (DiscreteMeasurableSpace.forall_measurableSet event), Set.encard,
    ENat.card_eq_coe_natCard]
  simp [Nat.card_eq_fintype_card]

/-- Split a fixed tape into independent equal-sized byte blocks. -/
def blockEquiv (count width : Nat) : Bytes (count*width) ≃ (Fin count → Bytes width) where
  toFun tape i := Vector.ofFn fun j => tape.get (Fin.mkDivMod i j)
  invFun blocks := Vector.ofFn fun i => (blocks i.divNat).get i.modNat
  left_inv tape := by
    ext i hi
    simp only [Vector.getElem_ofFn, Vector.get_ofFn, Fin.divNat_mkDivMod_modNat]
    rfl
  right_inv blocks := by
    funext i
    ext j hj
    simp only [Vector.getElem_ofFn, Vector.get_ofFn,
      Fin.divNat_mkDivMod, Fin.modNat_mkDivMod]
    rfl

end Blake3Prize.Submission.RomFiniteProbability
