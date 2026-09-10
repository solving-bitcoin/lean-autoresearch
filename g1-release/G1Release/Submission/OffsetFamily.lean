import G1Release.Protected.Target
import G1Release.Submission.TernaryFullWidth

namespace G1Release.Submission.OffsetFamily

open G1Release.Math
open G1Release.Submission.BalancedTernary
open G1Release.Submission.TernaryFullWidth

abbrev Hidden := G1Release.Protected.Private
abbrev Input := G1Release.Protected.Input
abbrev Point := BN254.G1

local instance : AddCommGroup BN254.G1 := inferInstance

def inputPoint (input : Input) : Point :=
  BN254.ofAffine input.val.1 input.val.2 input.property

def digits (hidden : Hidden) : Digits 161 :=
  encodeScalar hidden.2

def qPoint (hidden : Hidden) : Point :=
  hidden.1.toPoint

def mapAt (p : Hidden) (a : Input) : Point :=
  qPoint p + p.2.val • inputPoint a

/-- Independently owned little-endian offsets whose radix-three Horner sum is
the hidden constant `Q`. -/
@[ext] structure Fiber (hidden : Hidden) where
  values : List Point
  length_eq : values.length = 161
  total_eq : offsetTotal values = qPoint hidden

private theorem recompose_replicate_zero (count : Nat) :
    recompose (List.replicate count (0 : Point)) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, recompose_cons, ih]
      simp

/-- A canonical witness proves every offset fiber nonempty. -/
def canonical (hidden : Hidden) : Fiber hidden where
  values := qPoint hidden :: List.replicate 160 0
  length_eq := by simp
  total_eq := by
    change qPoint hidden + 3 • recompose (List.replicate 160 (0 : Point)) =
      qPoint hidden
    rw [recompose_replicate_zero]
    simp

instance (hidden : Hidden) : Nonempty (Fiber hidden) :=
  ⟨canonical hidden⟩

/-- Translate all offsets so every target trit map has exactly the source
selected value at one affine input. The existing minus-map translation is
applied to `-A`, which is the desired plus-map convention. -/
def translateValues (input : Input) (source target : Hidden)
    (offsets : List Point) : List Point :=
  translate offsets (digits source) (digits target) (-inputPoint input)

private theorem translateOffsets_length_of
    (offsets : List Point) (source target : List Digit) (point : Point)
    (hsource : offsets.length = source.length)
    (htarget : offsets.length = target.length) :
    (translateOffsets offsets source target point).length = offsets.length := by
  induction offsets generalizing source target with
  | nil =>
      cases source <;> cases target <;> simp_all [translateOffsets]
  | cons offset offsets ih =>
      cases source with
      | nil => simp at hsource
      | cons source sources =>
          cases target with
          | nil => simp at htarget
          | cons target targets =>
              simp only [translateOffsets, List.length_cons]
              congr 1
              apply ih sources targets
              · simpa using Nat.succ.inj hsource
              · simpa using Nat.succ.inj htarget

theorem translateValues_length (input : Input) (source target : Hidden)
    (offsets : List Point) (hlength : offsets.length = 161) :
    (translateValues input source target offsets).length = 161 := by
  rw [← hlength]
  apply translateOffsets_length_of offsets (digits source).values
    (digits target).values (-inputPoint input)
  · exact hlength.trans (digits source).length_eq.symm
  · exact hlength.trans (digits target).length_eq.symm

theorem translateValues_total (input : Input) (source target : Hidden)
    (hequal : mapAt source input = mapAt target input)
    (offsets : Fiber source) :
    offsetTotal (translateValues input source target offsets.values) =
      qPoint target := by
  have htranslate := offsetTotal_translate offsets.values
    (digits source) (digits target) (-inputPoint input) offsets.length_eq
  simp only [digits, decode_encodeScalar] at htranslate
  unfold translateValues
  simp only [digits]
  rw [htranslate, offsets.total_eq]
  change qPoint source + ((target.2.val : Int) - (source.2.val : Int)) •
      (-inputPoint input) = qPoint target
  change qPoint source + source.2.val • inputPoint input =
      qPoint target + target.2.val • inputPoint input at hequal
  have haction :
      ((target.2.val : Int) - (source.2.val : Int)) • (-inputPoint input) =
        source.2.val • inputPoint input - target.2.val • inputPoint input := by
    simp [sub_zsmul]
    rw [sub_eq_add_neg]
  rw [haction]
  calc
    qPoint source +
          (source.2.val • inputPoint input - target.2.val • inputPoint input) =
        (qPoint source + source.2.val • inputPoint input) -
          target.2.val • inputPoint input := by abel
    _ = (qPoint target + target.2.val • inputPoint input) -
          target.2.val • inputPoint input := by rw [hequal]
    _ = qPoint target := by abel

def forward (input : Input) (source target : Hidden)
    (hequal : mapAt source input = mapAt target input)
    (offsets : Fiber source) : Fiber target where
  values := translateValues input source target offsets.values
  length_eq := translateValues_length input source target offsets.values
    offsets.length_eq
  total_eq := translateValues_total input source target hequal offsets

theorem forward_swapped_forward (input : Input) (source target : Hidden)
    (hequal : mapAt source input = mapAt target input)
    (offsets : Fiber source) :
    forward input target source hequal.symm
        (forward input source target hequal offsets) = offsets := by
  apply Fiber.ext
  exact translate_source_target_source offsets.values
    (digits source) (digits target) (-inputPoint input) offsets.length_eq

/-- Explicit source/target offset-owner equivalence. -/
def equiv (input : Input) (source target : Hidden)
    (hequal : mapAt source input = mapAt target input) :
    Fiber source ≃ Fiber target where
  toFun := forward input source target hequal
  invFun := forward input target source hequal.symm
  left_inv := forward_swapped_forward input source target hequal
  right_inv := forward_swapped_forward input target source hequal.symm

/-- Every selected trit-map group output is preserved pointwise. -/
theorem selectedOutputs_preserved (input : Input) (source target : Hidden)
    (hequal : mapAt source input = mapAt target input)
    (offsets : Fiber source) :
    mapOutputs
        (equiv input source target hequal offsets).values
        (digits target).values (-inputPoint input) =
      mapOutputs offsets.values (digits source).values (-inputPoint input) := by
  exact mapOutputs_translate offsets.values (digits source) (digits target)
    (-inputPoint input) offsets.length_eq

end G1Release.Submission.OffsetFamily
