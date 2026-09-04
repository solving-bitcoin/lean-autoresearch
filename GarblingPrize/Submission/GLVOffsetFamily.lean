import GarblingPrize.Protected.Target
import GarblingPrize.Submission.EisensteinFullWidth

namespace GarblingPrize.Submission.GLVOffsetFamily

open GarblingPrize.Protected

abbrev ConcreteProfile := BN254.bn254
abbrev Hidden := HiddenInput ConcreteProfile
abbrev Input := AffineInput ConcreteProfile
abbrev Point := BN254.G1
abbrev Digit := EisensteinRadix.Digit

local instance concreteGroup : AddCommGroup Point :=
  ConcreteProfile.addCommGroup

def inputPoint (input : Input) : Point :=
  input.point

def digits (hidden : Hidden) : List Digit :=
  EisensteinRadix.digits 91 (EisensteinRadix.reduceScalar hidden.r.val)

theorem digits_length (hidden : Hidden) : (digits hidden).length = 91 := by
  simp [digits, EisensteinRadix.digits]

def qPoint (hidden : Hidden) : Point :=
  ConcreteProfile.outputEquiv hidden.Q

@[ext] structure Fiber (hidden : Hidden) where
  values : List Point
  length_eq : values.length = 91
  total_eq : EisensteinFullWidth.offsetTotal values = qPoint hidden

private theorem recompose_replicate_zero (count : Nat) :
    EisensteinFullWidth.recompose (List.replicate count (0 : Point)) = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.replicate_succ, EisensteinFullWidth.recompose_cons, ih]
      rw [EisensteinFullWidth.alphaPoint_zero, zero_add]

def canonical (hidden : Hidden) : Fiber hidden where
  values := qPoint hidden :: List.replicate 90 0
  length_eq := by simp
  total_eq := by
    change qPoint hidden +
      EisensteinFullWidth.alphaPoint
        (EisensteinFullWidth.recompose
          (List.replicate 90 (0 : Point))) = qPoint hidden
    rw [recompose_replicate_zero, EisensteinFullWidth.alphaPoint_zero,
      add_zero]

instance (hidden : Hidden) : Nonempty (Fiber hidden) := ⟨canonical hidden⟩

def translateValues (input : Input) (source target : Hidden)
    (offsets : List Point) : List Point :=
  EisensteinFullWidth.translateOffsets offsets (digits source)
    (digits target) (-inputPoint input)

private theorem translateOffsets_length_of
    (offsets : List Point) (source target : List Digit) (point : Point)
    (hsource : offsets.length = source.length)
    (htarget : offsets.length = target.length) :
    (EisensteinFullWidth.translateOffsets offsets source target point).length =
      offsets.length := by
  induction offsets generalizing source target with
  | nil =>
      cases source <;> cases target <;>
        simp_all [EisensteinFullWidth.translateOffsets]
  | cons offset offsets ih =>
      cases source with
      | nil => simp at hsource
      | cons source sources =>
          cases target with
          | nil => simp at htarget
          | cons target targets =>
              simp only [EisensteinFullWidth.translateOffsets,
                List.length_cons]
              congr 1
              apply ih sources targets
              · simpa using Nat.succ.inj hsource
              · simpa using Nat.succ.inj htarget

theorem translateValues_length (input : Input) (source target : Hidden)
    (offsets : List Point) (hlength : offsets.length = 91) :
    (translateValues input source target offsets).length = 91 := by
  rw [← hlength]
  apply translateOffsets_length_of offsets (digits source) (digits target)
    (-inputPoint input)
  · exact hlength.trans (digits_length source).symm
  · exact hlength.trans (digits_length target).symm

theorem translateValues_total (input : Input) (source target : Hidden)
    (hequal : reference ConcreteProfile source input =
      reference ConcreteProfile target input)
    (offsets : Fiber source) :
    EisensteinFullWidth.offsetTotal
        (translateValues input source target offsets.values) =
      qPoint target := by
  have htranslate := EisensteinFullWidth.offsetTotal_translateOffsets
    offsets.values (digits source) (digits target) (-inputPoint input)
    (offsets.length_eq.trans (digits_length source).symm)
    (offsets.length_eq.trans (digits_length target).symm)
  unfold translateValues
  rw [htranslate, offsets.total_eq]
  rw [show EisensteinFullWidth.recompose
        ((digits target).map fun digit =>
          EisensteinFullWidth.digitTerm digit (-inputPoint input)) =
        target.r.val • (-inputPoint input) by
      exact EisensteinFullWidth.recompose_scalar target.r (-inputPoint input),
    show EisensteinFullWidth.recompose
        ((digits source).map fun digit =>
          EisensteinFullWidth.digitTerm digit (-inputPoint input)) =
        source.r.val • (-inputPoint input) by
      exact EisensteinFullWidth.recompose_scalar source.r (-inputPoint input)]
  change qPoint source + source.r.val • inputPoint input =
    qPoint target + target.r.val • inputPoint input at hequal
  rw [EisensteinFullWidth.point_nsmul_neg,
    EisensteinFullWidth.point_nsmul_neg]
  calc
    qPoint source +
          (-(target.r.val • inputPoint input) -
            -(source.r.val • inputPoint input)) =
        (qPoint source + source.r.val • inputPoint input) -
          target.r.val • inputPoint input := by abel
    _ = (qPoint target + target.r.val • inputPoint input) -
          target.r.val • inputPoint input := by rw [hequal]
    _ = qPoint target := by abel

def forward (input : Input) (source target : Hidden)
    (hequal : reference ConcreteProfile source input =
      reference ConcreteProfile target input)
    (offsets : Fiber source) : Fiber target where
  values := translateValues input source target offsets.values
  length_eq := translateValues_length input source target offsets.values
    offsets.length_eq
  total_eq := translateValues_total input source target hequal offsets

theorem forward_swapped_forward (input : Input) (source target : Hidden)
    (hequal : reference ConcreteProfile source input =
      reference ConcreteProfile target input)
    (offsets : Fiber source) :
    forward input target source hequal.symm
        (forward input source target hequal offsets) = offsets := by
  apply Fiber.ext
  exact EisensteinFullWidth.translateOffsets_source_target_source offsets.values
    (digits source) (digits target) (-inputPoint input)
    (offsets.length_eq.trans (digits_length source).symm)
    (offsets.length_eq.trans (digits_length target).symm)

def equiv (input : Input) (source target : Hidden)
    (hequal : reference ConcreteProfile source input =
      reference ConcreteProfile target input) :
    Fiber source ≃ Fiber target where
  toFun := forward input source target hequal
  invFun := forward input target source hequal.symm
  left_inv := forward_swapped_forward input source target hequal
  right_inv := forward_swapped_forward input target source hequal.symm

theorem selectedOutputs_preserved (input : Input) (source target : Hidden)
    (hequal : reference ConcreteProfile source input =
      reference ConcreteProfile target input)
    (offsets : Fiber source) :
    EisensteinFullWidth.mapOutputs
        (equiv input source target hequal offsets).values
        (digits target) (-inputPoint input) =
      EisensteinFullWidth.mapOutputs offsets.values
        (digits source) (-inputPoint input) := by
  exact EisensteinFullWidth.mapOutputs_translateOffsets offsets.values
    (digits source) (digits target) (-inputPoint input)
    (offsets.length_eq.trans (digits_length source).symm)
    (offsets.length_eq.trans (digits_length target).symm)

end GarblingPrize.Submission.GLVOffsetFamily
