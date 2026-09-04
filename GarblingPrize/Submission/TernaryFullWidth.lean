import GarblingPrize.Submission.BalancedTernary

namespace GarblingPrize.Submission.TernaryFullWidth

/-!
# Full-width balanced-ternary recomposition

This proof-only module connects the executable balanced-ternary codec to an
arbitrary additive commutative group.  Lists are little endian: the head is
the coefficient of `3^0`, and the tail is multiplied by three.

The definitions in this file are deliberately `noncomputable`.  Their only
role is to state and prove the algebraic semantics of executable projective
map families; executable code continues to use fixed-width byte and
projective recurrences.
-/

open GarblingPrize.Submission.BalancedTernary

noncomputable section

variable {G : Type*} [AddCommGroup G]

/-- Little-endian radix-three Horner recomposition in an additive group. -/
def recompose : List G → G
  | [] => 0
  | head :: tail => head + 3 • recompose tail

@[simp] theorem recompose_nil : recompose ([] : List G) = 0 := rfl

@[simp] theorem recompose_cons (head : G) (tail : List G) :
    recompose (head :: tail) = head + 3 • recompose tail := rfl

/-- The group term denoted by one balanced ternary digit. -/
def digitTerm (digit : Digit) (point : G) : G :=
  digit.value • point

/-- Recompose the signed multiples selected by a little-endian digit list. -/
def signedRecompositionList (digits : List Digit) (point : G) : G :=
  recompose (digits.map fun digit => digitTerm digit point)

/-- Horner recomposition commutes with the integer action on a fixed point. -/
theorem signedRecompositionList_eq (digits : List Digit) (point : G) :
    signedRecompositionList digits point =
      GarblingPrize.Submission.BalancedTernary.Digits.decodeList digits • point := by
  induction digits with
  | nil => simp [signedRecompositionList,
      GarblingPrize.Submission.BalancedTernary.Digits.decodeList]
  | cons digit tail ih =>
      simp only [signedRecompositionList, List.map_cons, recompose_cons,
        digitTerm,
        GarblingPrize.Submission.BalancedTernary.Digits.decodeList]
      change
        digit.value • point + 3 • signedRecompositionList tail point =
          (digit.value + 3 *
            GarblingPrize.Submission.BalancedTernary.Digits.decodeList tail) • point
      rw [ih, add_zsmul, mul_zsmul]
      exact congrArg (digit.value • point + ·)
        (ofNat_zsmul
          (GarblingPrize.Submission.BalancedTernary.Digits.decodeList tail • point) 3).symm

/-- Fixed-width form of `signedRecompositionList`. -/
def signedRecomposition (digits : Digits width) (point : G) : G :=
  signedRecompositionList digits.values point

/-- A fixed-width balanced word acts by its exact decoded integer. -/
theorem signedRecomposition_eq (digits : Digits width) (point : G) :
    signedRecomposition digits point = digits.decode • point := by
  exact signedRecompositionList_eq digits.values point

/-- The canonical full-width BN254 scalar codec recomposes to natural
scalar multiplication, with no modular or truncating step. -/
theorem signedRecomposition_encodeScalar
    (scalar : Fin GarblingPrize.Protected.scalarFieldModulus) (point : G) :
    signedRecomposition (encodeScalar scalar) point = scalar.val • point := by
  rw [signedRecomposition_eq, decode_encodeScalar]
  simp

/-- The canonical unsigned 32-bit codec recomposes to natural scalar
multiplication, with no modular or truncating step. -/
theorem signedRecomposition_encodeUInt32
    (value : Fin (2 ^ 32)) (point : G) :
    signedRecomposition (encodeUInt32 value) point = value.val • point := by
  rw [signedRecomposition_eq, decode_encodeUInt32]
  simp

/-! ## Offset-plus-signed-digit maps -/

/-- Independently owned offsets use the same little-endian radix-three
recomposition as the signed digit terms. -/
def offsetTotal (offsets : List G) : G :=
  recompose offsets

/-- One public map output: an independently owned offset minus the signed
digit multiple of the proof point. -/
def mapOutput (offset : G) (digit : Digit) (point : G) : G :=
  offset - digit.value • point

/-- Pair every offset with the corresponding little-endian signed digit.
The length hypothesis on the semantic theorems rules out truncation by
`List.zipWith`. -/
def mapOutputs (offsets : List G) (digits : List Digit) (point : G) : List G :=
  List.zipWith (fun offset digit => mapOutput offset digit point)
    offsets digits

/-- Public Horner recomposition of the already-masked map outputs. -/
def outputList (offsets : List G) (digits : List Digit) (point : G) : G :=
  recompose (mapOutputs offsets digits point)

/-- Recomposition of offset-minus-digit maps is exactly the recomposed
offset owner minus the decoded scalar multiple of the proof point. -/
theorem outputList_eq (offsets : List G) (digits : List Digit) (point : G)
    (hlength : offsets.length = digits.length) :
    outputList offsets digits point =
      offsetTotal offsets -
        GarblingPrize.Submission.BalancedTernary.Digits.decodeList digits • point := by
  induction offsets generalizing digits with
  | nil =>
      cases digits with
      | nil =>
          simp [outputList, mapOutputs, offsetTotal,
            GarblingPrize.Submission.BalancedTernary.Digits.decodeList]
      | cons digit digits => simp at hlength
  | cons offset offsets ih =>
      cases digits with
      | nil => simp at hlength
      | cons digit digits =>
          have htail : offsets.length = digits.length := by
            simpa using Nat.succ.inj hlength
          simp only [outputList, mapOutputs, List.zipWith_cons_cons,
            recompose_cons]
          change
            mapOutput offset digit point +
                3 • outputList offsets digits point =
              offsetTotal (offset :: offsets) -
                (digit.value + 3 *
                    GarblingPrize.Submission.BalancedTernary.Digits.decodeList digits) •
                  point
          rw [ih digits htail]
          simp only [mapOutput, offsetTotal, recompose_cons, add_zsmul,
            mul_zsmul, sub_eq_add_neg, neg_add_rev, nsmul_add]
          abel

/-- Fixed-width wrapper around `outputList`. -/
def output (offsets : List G) (digits : Digits width) (point : G) : G :=
  outputList offsets digits.values point

/-- Fixed-width offset-plus-signed-digit recomposition. -/
theorem output_eq (offsets : List G) (digits : Digits width) (point : G)
    (hlength : offsets.length = width) :
    output offsets digits point =
      offsetTotal offsets - digits.decode • point := by
  exact outputList_eq offsets digits.values point
    (hlength.trans digits.length_eq.symm)

/-- Exact natural-scalar specialization for the BN254 scalar encoding. -/
theorem output_encodeScalar (offsets : List G)
    (scalar : Fin GarblingPrize.Protected.scalarFieldModulus) (point : G)
    (hlength : offsets.length = 161) :
    output offsets (encodeScalar scalar) point =
      offsetTotal offsets - scalar.val • point := by
  rw [output_eq offsets (encodeScalar scalar) point hlength,
    decode_encodeScalar]
  simp

/-- Exact natural-scalar specialization for the unsigned 32-bit encoding. -/
theorem output_encodeUInt32 (offsets : List G)
    (value : Fin (2 ^ 32)) (point : G)
    (hlength : offsets.length = 21) :
    output offsets (encodeUInt32 value) point =
      offsetTotal offsets - value.val • point := by
  rw [output_eq offsets (encodeUInt32 value) point hlength,
    decode_encodeUInt32]
  simp

/-! ## Exact offset translation -/

/-- Translate one offset when changing its active digit. -/
def translatedOffset (source target : Digit) (point offset : G) : G :=
  offset + (target.value - source.value) • point

/-- The source map output is literally preserved after translating its
offset and selecting the target digit. -/
theorem mapOutput_translatedOffset (source target : Digit) (point offset : G) :
    mapOutput (translatedOffset source target point offset) target point =
      mapOutput offset source point := by
  unfold mapOutput translatedOffset
  rw [sub_zsmul]
  abel

/-- Pointwise translation of equally long offset and digit lists. -/
def translateOffsets : List G → List Digit → List Digit → G → List G
  | offset :: offsets, source :: sources, target :: targets, point =>
      translatedOffset source target point offset ::
        translateOffsets offsets sources targets point
  | _, _, _, _ => []

/-- Translating all offsets preserves every active map output, not merely
their final recomposition. -/
theorem mapOutputs_translateOffsets (offsets : List G)
    (source target : List Digit) (point : G)
    (hsource : offsets.length = source.length)
    (htarget : offsets.length = target.length) :
    mapOutputs (translateOffsets offsets source target point) target point =
      mapOutputs offsets source point := by
  induction offsets generalizing source target with
  | nil =>
      cases source with
      | cons source sources => simp at hsource
      | nil =>
          cases target with
          | cons target targets => simp at htarget
          | nil => rfl
  | cons offset offsets ih =>
      cases source with
      | nil => simp at hsource
      | cons source sources =>
          cases target with
          | nil => simp at htarget
          | cons target targets =>
              have hs : offsets.length = sources.length := by
                simpa using Nat.succ.inj hsource
              have ht : offsets.length = targets.length := by
                simpa using Nat.succ.inj htarget
              simp only [translateOffsets, mapOutputs, List.zipWith_cons_cons,
                mapOutput_translatedOffset]
              exact congrArg (mapOutput offset source point :: ·)
                (ih sources targets hs ht)

/-- The translated offset owner changes by the decoded target/source scalar
difference. -/
theorem offsetTotal_translateOffsets (offsets : List G)
    (source target : List Digit) (point : G)
    (hsource : offsets.length = source.length)
    (htarget : offsets.length = target.length) :
    offsetTotal (translateOffsets offsets source target point) =
      offsetTotal offsets +
        (GarblingPrize.Submission.BalancedTernary.Digits.decodeList target -
          GarblingPrize.Submission.BalancedTernary.Digits.decodeList source) • point := by
  induction offsets generalizing source target with
  | nil =>
      cases source with
      | cons source sources => simp at hsource
      | nil =>
          cases target with
          | cons target targets => simp at htarget
          | nil =>
              simp [offsetTotal, translateOffsets,
                GarblingPrize.Submission.BalancedTernary.Digits.decodeList]
  | cons offset offsets ih =>
      cases source with
      | nil => simp at hsource
      | cons source sources =>
          cases target with
          | nil => simp at htarget
          | cons target targets =>
              have hs : offsets.length = sources.length := by
                simpa using Nat.succ.inj hsource
              have ht : offsets.length = targets.length := by
                simpa using Nat.succ.inj htarget
              simp only [translateOffsets, offsetTotal, recompose_cons]
              change
                translatedOffset source target point offset +
                    3 • offsetTotal
                      (translateOffsets offsets sources targets point) =
                  offset + 3 • offsetTotal offsets +
                    (GarblingPrize.Submission.BalancedTernary.Digits.decodeList
                          (target :: targets) -
                        GarblingPrize.Submission.BalancedTernary.Digits.decodeList
                          (source :: sources)) • point
              rw [ih sources targets hs ht]
              simp only [translatedOffset, offsetTotal,
                GarblingPrize.Submission.BalancedTernary.Digits.decodeList,
                add_zsmul, mul_zsmul, nsmul_add,
                sub_eq_add_neg, neg_add_rev, neg_zsmul]
              abel

/-- Complete fixed-width translation wrapper. -/
def translate (offsets : List G) (source target : Digits width)
    (point : G) : List G :=
  translateOffsets offsets source.values target.values point

/-- Fixed-width translation preserves the complete vector of active map
outputs. -/
theorem mapOutputs_translate (offsets : List G)
    (source target : Digits width) (point : G)
    (hlength : offsets.length = width) :
    mapOutputs (translate offsets source target point) target.values point =
      mapOutputs offsets source.values point := by
  apply mapOutputs_translateOffsets
  · exact hlength.trans source.length_eq.symm
  · exact hlength.trans target.length_eq.symm

/-- Fixed-width translation preserves the public Horner result. -/
theorem output_translate (offsets : List G)
    (source target : Digits width) (point : G)
    (hlength : offsets.length = width) :
    output (translate offsets source target point) target point =
      output offsets source point := by
  unfold output outputList
  rw [mapOutputs_translate offsets source target point hlength]

/-- Fixed-width offset-total translation equation. -/
theorem offsetTotal_translate (offsets : List G)
    (source target : Digits width) (point : G)
    (hlength : offsets.length = width) :
    offsetTotal (translate offsets source target point) =
      offsetTotal offsets + (target.decode - source.decode) • point := by
  apply offsetTotal_translateOffsets
  · exact hlength.trans source.length_eq.symm
  · exact hlength.trans target.length_eq.symm

/-- Swapping source and target list translations restores every offset. -/
theorem translateOffsets_source_target_source (offsets : List G)
    (source target : List Digit) (point : G)
    (hsource : offsets.length = source.length)
    (htarget : offsets.length = target.length) :
    translateOffsets
        (translateOffsets offsets source target point) target source point =
      offsets := by
  induction offsets generalizing source target with
  | nil =>
      cases source with
      | cons source sources => simp at hsource
      | nil =>
          cases target with
          | cons target targets => simp at htarget
          | nil => rfl
  | cons offset offsets ih =>
      cases source with
      | nil => simp at hsource
      | cons source sources =>
          cases target with
          | nil => simp at htarget
          | cons target targets =>
              have hs : offsets.length = sources.length := by
                simpa using Nat.succ.inj hsource
              have ht : offsets.length = targets.length := by
                simpa using Nat.succ.inj htarget
              simp only [translateOffsets]
              rw [ih sources targets hs ht]
              congr 1
              unfold translatedOffset
              rw [sub_zsmul, sub_zsmul]
              abel

/-- Swapping source and target fixed-width translations restores every
offset. -/
theorem translate_source_target_source (offsets : List G)
    (source target : Digits width) (point : G)
    (hlength : offsets.length = width) :
    translate (translate offsets source target point) target source point =
      offsets := by
  unfold translate
  apply translateOffsets_source_target_source
  · exact hlength.trans source.length_eq.symm
  · exact hlength.trans target.length_eq.symm

end

end GarblingPrize.Submission.TernaryFullWidth
