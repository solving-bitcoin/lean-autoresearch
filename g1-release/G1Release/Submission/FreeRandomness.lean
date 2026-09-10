import G1Release.Submission.RandomnessLaw

/-! Independent coordinates for the ideal arithmetic randomness. The head
of each additive mask fiber is derived, so no rejection is needed to satisfy
its defining sum. -/
namespace G1Release.Submission.Randomized
open G1Release.Math G1Release.Protected
open scoped BigOperators
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

abbrev OffsetTail := { values : List OffsetFamily.Point // values.length = 160 }

def offsetTailEquiv : (Fin 160 → OffsetFamily.Point) ≃ OffsetTail where
  toFun values := ⟨List.ofFn values, List.length_ofFn⟩
  invFun values := fun index => values.1.get ⟨index.val, by
    rw [values.2]
    exact index.isLt⟩
  left_inv values := by
    funext index
    change (List.ofFn values).get _ = values index
    rw [List.get_ofFn]
    congr
  right_inv values := by
    apply Subtype.ext
    apply List.ext_get
    · rw [List.length_ofFn, values.2]
    · intro index hleft hright
      rw [List.get_ofFn]
      congr

def offsetsFromTail (hidden : Hidden) (tail : OffsetTail) :
    OffsetFamily.Fiber hidden :=
  let values := tail.1
  { values := (OffsetFamily.qPoint hidden -
        3 • TernaryFullWidth.recompose values) :: values
    length_eq := by rw [List.length_cons, tail.2]
    total_eq := by
      change (OffsetFamily.qPoint hidden -
          3 • TernaryFullWidth.recompose values) +
        3 • TernaryFullWidth.recompose values = OffsetFamily.qPoint hidden
      abel }

def tailFromOffsets {hidden : Hidden} (offsets : OffsetFamily.Fiber hidden) :
    OffsetTail :=
  ⟨offsets.values.tail, by rw [List.length_tail, offsets.length_eq]⟩

@[simp] theorem tailFromOffsets_offsetsFromTail (hidden : Hidden)
    (tail : OffsetTail) :
    tailFromOffsets (offsetsFromTail hidden tail) = tail := by
  apply Subtype.ext
  rfl

theorem offsetsFromTail_tailFromOffsets (hidden : Hidden)
    (offsets : OffsetFamily.Fiber hidden) :
    offsetsFromTail hidden (tailFromOffsets offsets) = offsets := by
  apply OffsetFamily.Fiber.ext
  change (OffsetFamily.qPoint hidden -
        3 • TernaryFullWidth.recompose offsets.values.tail) ::
      offsets.values.tail = offsets.values
  cases hvalues : offsets.values with
  | nil =>
      have hlength := offsets.length_eq
      rw [hvalues] at hlength
      simp at hlength
  | cons head tail =>
      have htotal := offsets.total_eq
      rw [hvalues] at htotal
      simp only [TernaryFullWidth.offsetTotal,
        TernaryFullWidth.recompose_cons] at htotal
      simp only [hvalues, List.tail_cons]
      congr 1
      change OffsetFamily.qPoint hidden -
          3 • TernaryFullWidth.recompose tail = head
      rw [← htotal]
      abel

noncomputable def offsetsEquiv (hidden : Hidden) :
    OffsetTail ≃ OffsetFamily.Fiber hidden where
  toFun := offsetsFromTail hidden
  invFun := tailFromOffsets
  left_inv := tailFromOffsets_offsetsFromTail hidden
  right_inv := offsetsFromTail_tailFromOffsets hidden

def tableMaskFromFree (constant : BN254.Fq)
    (free : Fin 253 → BN254.Fq) : AffineTable.MaskFiber constant :=
  let final := constant - ∑ slot, free slot
  ⟨Fin.lastCases final free, by
    change ∑ i : Fin (253 + 1), Fin.lastCases final free i = constant
    rw [Fin.sum_univ_castSucc, Fin.lastCases_last]
    simp [final]⟩

def tableMaskFree {constant : BN254.Fq}
    (mask : AffineTable.MaskFiber constant) : Fin 253 → BN254.Fq :=
  fun slot => mask.1 slot.castSucc

@[simp] theorem tableMaskFree_fromFree (constant : BN254.Fq)
    (free : Fin 253 → BN254.Fq) :
    tableMaskFree (tableMaskFromFree constant free) = free := by
  funext slot
  simp [tableMaskFree, tableMaskFromFree]

theorem tableMaskFromFree_free {constant : BN254.Fq}
    (mask : AffineTable.MaskFiber constant) :
    tableMaskFromFree constant (tableMaskFree mask) = mask := by
  apply Subtype.ext
  funext slot
  refine Fin.lastCases ?_ (fun index => ?_) slot
  · change constant - ∑ index : Fin 253, mask.1 index.castSucc =
      mask.1 (Fin.last 253)
    have hsum := mask.2
    rw [Fin.sum_univ_castSucc] at hsum
    rw [sub_eq_iff_eq_add, add_comm]
    exact hsum.symm
  · simp [tableMaskFromFree, tableMaskFree]

def tableMaskEquiv (constant : BN254.Fq) :
    (Fin 253 → BN254.Fq) ≃ AffineTable.MaskFiber constant where
  toFun := tableMaskFromFree constant
  invFun := tableMaskFree
  left_inv := tableMaskFree_fromFree constant
  right_inv := tableMaskFromFree_free

def chainsFromFree (values : Fin 8 → BN254.Fq) :
    ProjectiveMap.ChainMasks BN254.Fq where
  shared := values 0
  xCross := values 1
  xOuter := values 2
  yCubic := values 3
  yQuadratic := values 4
  zSquare := values 5
  zCross := values 6
  zLinear := values 7

def chainsFree (masks : ProjectiveMap.ChainMasks BN254.Fq) :
    Fin 8 → BN254.Fq
  | ⟨0, _⟩ => masks.shared
  | ⟨1, _⟩ => masks.xCross
  | ⟨2, _⟩ => masks.xOuter
  | ⟨3, _⟩ => masks.yCubic
  | ⟨4, _⟩ => masks.yQuadratic
  | ⟨5, _⟩ => masks.zSquare
  | ⟨6, _⟩ => masks.zCross
  | ⟨7, _⟩ => masks.zLinear

@[simp] theorem chainsFree_fromFree (values : Fin 8 → BN254.Fq) :
    chainsFree (chainsFromFree values) = values := by
  funext index
  fin_cases index <;> rfl

@[simp] theorem chainsFromFree_free
    (masks : ProjectiveMap.ChainMasks BN254.Fq) :
    chainsFromFree (chainsFree masks) = masks := by
  apply ProjectiveMap.ChainMasks.ext <;> rfl

structure FreeRandomness where
  offsets : OffsetTail
  scales : Fin 161 → BN254.Fqˣ
  chains : Fin 161 → Fin 8 → BN254.Fq
  tableMasks : Fin 161 → ProjectiveMap.TableKind → Fin 253 → BN254.Fq

@[ext] theorem FreeRandomness.ext (left right : FreeRandomness)
    (hoffsets : left.offsets = right.offsets)
    (hscales : left.scales = right.scales)
    (hchains : left.chains = right.chains)
    (htables : left.tableMasks = right.tableMasks) : left = right := by
  cases left
  cases right
  cases hoffsets
  cases hscales
  cases hchains
  cases htables
  rfl

def randomnessFromFree (hidden : Hidden) (free : FreeRandomness) :
    Randomness hidden :=
  let offsets := offsetsFromTail hidden free.offsets
  { offsets
    scales := free.scales
    chains := fun index => chainsFromFree (free.chains index)
    tableMasks := fun index kind =>
      (tableMaskFromFree
        ((mapHidden hidden offsets free.scales
          (fun index => chainsFromFree (free.chains index)) index).params
          kind).constant
        (free.tableMasks index kind)).1
    tableMasks_sum := fun index kind =>
      (tableMaskFromFree
        ((mapHidden hidden offsets free.scales
          (fun index => chainsFromFree (free.chains index)) index).params
          kind).constant
        (free.tableMasks index kind)).2 }

def freeFromRandomness {hidden : Hidden} (randomness : Randomness hidden) :
    FreeRandomness where
  offsets := tailFromOffsets randomness.offsets
  scales := randomness.scales
  chains := fun index => chainsFree (randomness.chains index)
  tableMasks := fun index kind => tableMaskFree
    (⟨randomness.tableMasks index kind,
      randomness.tableMasks_sum index kind⟩ :
      AffineTable.MaskFiber
        ((mapHidden hidden randomness.offsets randomness.scales
          randomness.chains index).params kind).constant)

@[simp] theorem freeFromRandomness_randomnessFromFree (hidden : Hidden)
    (free : FreeRandomness) :
    freeFromRandomness (randomnessFromFree hidden free) = free := by
  apply FreeRandomness.ext
  · exact (offsetsEquiv hidden).left_inv free.offsets
  · rfl
  · funext index
    exact chainsFree_fromFree _
  · funext index kind
    exact tableMaskFree_fromFree _ _

theorem randomnessFromFree_freeFromRandomness (hidden : Hidden)
    (randomness : Randomness hidden) :
    randomnessFromFree hidden (freeFromRandomness randomness) = randomness := by
  apply Randomness.ext
  · exact (offsetsEquiv hidden).right_inv randomness.offsets
  · rfl
  · funext index
    exact chainsFromFree_free _
  · funext index kind
    have hoffsets := (offsetsEquiv hidden).right_inv randomness.offsets
    dsimp only [freeFromRandomness]
    change (tableMaskFromFree _ (tableMaskFree
      (⟨randomness.tableMasks index kind,
        randomness.tableMasks_sum index kind⟩ :
        AffineTable.MaskFiber _))).1 = randomness.tableMasks index kind
    rw [show offsetsFromTail hidden (tailFromOffsets randomness.offsets) =
      randomness.offsets from hoffsets]
    exact congrArg Subtype.val (tableMaskFromFree_free
      (⟨randomness.tableMasks index kind,
        randomness.tableMasks_sum index kind⟩ :
        AffineTable.MaskFiber _))

def freeRandomnessEquiv (hidden : Hidden) :
    FreeRandomness ≃ Randomness hidden where
  toFun := randomnessFromFree hidden
  invFun := freeFromRandomness
  left_inv := freeFromRandomness_randomnessFromFree hidden
  right_inv := randomnessFromFree_freeFromRandomness hidden


end G1Release.Submission.Randomized
