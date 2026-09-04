import GarblingPrize.Submission.CompactScheme

namespace GarblingPrize.Submission.CompactOracleLaw

open GarblingPrize.Protected
open GarblingPrize.Submission
open GarblingPrize.Submission.CompactScheme

local instance concreteGroup : AddCommGroup BN254.G1 :=
  BN254.bn254.addCommGroup
local instance profileGroup : AddCommGroup Profile.G1 := concreteGroup

open MeasureTheory ProbabilityTheory

noncomputable instance (hidden : Hidden) :
    MeasurableSpace (Randomness hidden) := ⊤

noncomputable instance (hidden : Hidden) :
    DiscreteMeasurableSpace (Randomness hidden) where
  forall_measurableSet := fun _ => MeasurableSpace.measurableSet_top

noncomputable def randomnessLaw (hidden : Hidden) :
    Measure (Randomness hidden) := uniformOn Set.univ

theorem prod_uniform_univ {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [DiscreteMeasurableSpace α] [DiscreteMeasurableSpace β]
    [Finite α] [Finite β] [Nonempty α] [Nonempty β] :
    (uniformOn (Set.univ : Set α)).prod (uniformOn (Set.univ : Set β)) =
      uniformOn (Set.univ : Set (α × β)) := by
  classical
  letI := Fintype.ofFinite α
  letI := Fintype.ofFinite β
  apply Measure.ext_of_singleton
  intro value
  rw [show ({value} : Set (α × β)) = {value.1} ×ˢ {value.2} by simp]
  rw [Measure.prod_prod]
  simp [uniformOn_univ, ENNReal.mul_inv]

theorem infinitePi_uniform_univ {ι Ω : Type*}
    [Fintype ι] [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    [Finite Ω] [Nonempty Ω] :
    Measure.infinitePi (fun _ : ι => uniformOn (Set.univ : Set Ω)) =
      uniformOn (Set.univ : Set (ι → Ω)) := by
  rw [Measure.infinitePi_eq_pi]
  rw [← ProbabilityTheory.uniformOn_pi
    (f := fun _ : ι => (Set.univ : Set Ω))]
  simp

theorem infinitePi_uniform_univ_dependent {ι : Type*} (Ω : ι → Type*)
    [Fintype ι] [∀ i, MeasurableSpace (Ω i)]
    [∀ i, DiscreteMeasurableSpace (Ω i)]
    [∀ i, Finite (Ω i)] [∀ i, Nonempty (Ω i)] :
    Measure.infinitePi
        (fun i => uniformOn (Set.univ : Set (Ω i))) =
      uniformOn (Set.univ : Set ((i : ι) → Ω i)) := by
  classical
  letI (i : ι) := Fintype.ofFinite (Ω i)
  rw [Measure.infinitePi_eq_pi]
  apply Measure.ext_of_singleton
  intro value
  rw [Measure.pi_singleton]
  simp only [uniformOn_univ, Measure.smul_apply, MeasurableSet.singleton,
    Measure.count_apply, Set.encard_singleton, ENNReal.smul_def,
    one_mul, Fintype.card_pi, Nat.cast_prod]
  symm
  simp only [ENat.toENNReal_one]
  rw [show (1 : ENNReal) / ∏ i, (Fintype.card (Ω i) : ENNReal) =
      (∏ i, (Fintype.card (Ω i) : ENNReal))⁻¹ by
    exact one_div _]
  conv_rhs =>
    enter [2, i]
    rw [show (1 : ENNReal) / (Fintype.card (Ω i) : ENNReal) =
        ((Fintype.card (Ω i) : ENNReal))⁻¹ by exact one_div _]
  apply ENNReal.prod_inv_distrib
  intro i hi j hj hij
  left
  exact_mod_cast Fintype.card_ne_zero


theorem standardGenerator_order :
    addOrderOf standardGenerator = scalarFieldModulus := by
  rw [show standardGenerator =
      G1GeneratorCertificateBase.generatorPoint by
    unfold standardGenerator G1GeneratorCertificateBase.generatorPoint
      G1GeneratorCertificateBase.generator G1CertificateBase.semantic
      G1CertificateBase.affine FormulaSemantics.Law.pointOfInput
    rfl]
  exact G1Cardinality.generator_addOrderOf

noncomputable def generatorEquiv : Fin scalarFieldModulus ≃ BN254.G1 :=
  Equiv.ofBijective
    (fun scalar : Fin scalarFieldModulus => scalar.val • standardGenerator)
    ((Nat.bijective_iff_injective_and_card _).2 ⟨by
      intro left right hequal
      apply Fin.ext
      exact nsmul_injOn_Iio_addOrderOf
        (by simpa [standardGenerator_order] using left.isLt)
        (by simpa [standardGenerator_order] using right.isLt)
        hequal,
      by
        rw [Nat.card_fin, G1Cardinality.pointCardinality]⟩)

@[simp] theorem generatorEquiv_apply (scalar : Fin scalarFieldModulus) :
    generatorEquiv scalar = scalar.val • standardGenerator := rfl

private theorem baseFieldUnits_positive : 0 < baseFieldModulus - 1 := by
  norm_num [baseFieldModulus]

private theorem unitValue_positive (value : (ZMod baseFieldModulus)ˣ) :
    0 < value.val.val := by
  have hne : value.val ≠ 0 := Units.ne_zero value
  have hval : value.val.val ≠ 0 := by
    intro hzero
    apply hne
    apply ZMod.val_injective
    simpa [hzero]
  omega

private theorem unitValue_pred_lt (value : (ZMod baseFieldModulus)ˣ) :
    value.val.val - 1 < baseFieldModulus - 1 := by
  have hlt := value.val.val_lt
  have hpos := unitValue_positive value
  omega

noncomputable def unitEquiv :
    Fin (baseFieldModulus - 1) ≃ (ZMod baseFieldModulus)ˣ where
  toFun value := Units.mk0 ((value.val + 1 : Nat) : ZMod baseFieldModulus) (by
    intro hzero
    have hdvd : baseFieldModulus ∣ value.val + 1 :=
      (ZMod.natCast_eq_zero_iff _ _).mp hzero
    have hle := Nat.le_of_dvd (by omega : 0 < value.val + 1) hdvd
    omega)
  invFun value := ⟨value.val.val - 1, unitValue_pred_lt value⟩
  left_inv value := by
    apply Fin.ext
    change (((value.val + 1 : Nat) : ZMod baseFieldModulus).val - 1) =
      value.val
    rw [ZMod.val_natCast_of_lt]
    · omega
    · omega
  right_inv value := by
    have hpos := unitValue_positive value
    apply Units.ext
    apply ZMod.val_injective
    change (((value.val.val - 1 + 1 : Nat) : ZMod baseFieldModulus).val) =
      value.val.val
    rw [ZMod.val_natCast_of_lt]
    · omega
    · have hlt := value.val.val_lt
      omega

@[simp] theorem unitEquiv_apply_val (value : Fin (baseFieldModulus - 1)) :
    ((unitEquiv value : (ZMod baseFieldModulus)ˣ) : ZMod baseFieldModulus) =
      (value.val + 1 : Nat) := rfl

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
    (free : Fin 253 → BN254.Fq) : IdealAffineTable.MaskFiber constant :=
  let final := constant - ∑ slot, free slot
  ⟨Fin.lastCases final free, by
    change ∑ i : Fin (253 + 1), Fin.lastCases final free i = constant
    rw [Fin.sum_univ_castSucc, Fin.lastCases_last]
    simp [final]⟩

def tableMaskFree {constant : BN254.Fq}
    (mask : IdealAffineTable.MaskFiber constant) : Fin 253 → BN254.Fq :=
  fun slot => mask.1 slot.castSucc

@[simp] theorem tableMaskFree_fromFree (constant : BN254.Fq)
    (free : Fin 253 → BN254.Fq) :
    tableMaskFree (tableMaskFromFree constant free) = free := by
  funext slot
  simp [tableMaskFree, tableMaskFromFree]

theorem tableMaskFromFree_free {constant : BN254.Fq}
    (mask : IdealAffineTable.MaskFiber constant) :
    tableMaskFromFree constant (tableMaskFree mask) = mask := by
  apply Subtype.ext
  funext slot
  refine Fin.lastCases ?_ (fun index => ?_) slot
  · change constant - ∑ index : Fin 253, mask.1 index.castSucc =
      mask.1 (Fin.last 253)
    have hsum := mask.2
    unfold IdealAffineTable.tableWidth at hsum
    rw [Fin.sum_univ_castSucc] at hsum
    rw [sub_eq_iff_eq_add, add_comm]
    exact hsum.symm
  · simp [tableMaskFromFree, tableMaskFree]

def tableMaskEquiv (constant : BN254.Fq) :
    (Fin 253 → BN254.Fq) ≃ IdealAffineTable.MaskFiber constant where
  toFun := tableMaskFromFree constant
  invFun := tableMaskFree
  left_inv := tableMaskFree_fromFree constant
  right_inv := tableMaskFromFree_free

def chainMasksFromFree (values : Fin 8 → BN254.Fq) :
    ProjectiveMap.ChainMasks BN254.Fq where
  shared := values 0
  xCross := values 1
  xOuter := values 2
  yCubic := values 3
  yQuadratic := values 4
  zSquare := values 5
  zCross := values 6
  zLinear := values 7

def chainMasksFree (masks : ProjectiveMap.ChainMasks BN254.Fq) :
    Fin 8 → BN254.Fq
  | ⟨0, _⟩ => masks.shared
  | ⟨1, _⟩ => masks.xCross
  | ⟨2, _⟩ => masks.xOuter
  | ⟨3, _⟩ => masks.yCubic
  | ⟨4, _⟩ => masks.yQuadratic
  | ⟨5, _⟩ => masks.zSquare
  | ⟨6, _⟩ => masks.zCross
  | ⟨7, _⟩ => masks.zLinear

@[simp] theorem chainMasksFree_fromFree (values : Fin 8 → BN254.Fq) :
    chainMasksFree (chainMasksFromFree values) = values := by
  funext index
  fin_cases index <;> rfl

@[simp] theorem chainMasksFromFree_free
    (masks : ProjectiveMap.ChainMasks BN254.Fq) :
    chainMasksFromFree (chainMasksFree masks) = masks := by
  apply ProjectiveMap.ChainMasks.ext <;> rfl

structure FreeRandomness where
  offsets : OffsetTail
  randomizers : Fin 161 → BN254.Fqˣ
  chainMasks : Fin 161 → Fin 8 → BN254.Fq
  tableMasks : Fin 161 → ProjectiveMap.TableKind → Fin 253 → BN254.Fq

@[ext] theorem FreeRandomness.ext (left right : FreeRandomness)
    (hoffsets : left.offsets = right.offsets)
    (hrandomizers : left.randomizers = right.randomizers)
    (hchains : left.chainMasks = right.chainMasks)
    (htables : left.tableMasks = right.tableMasks) : left = right := by
  cases left
  cases right
  cases hoffsets
  cases hrandomizers
  cases hchains
  cases htables
  rfl

def randomnessFromFree (hidden : Hidden) (free : FreeRandomness) :
    Randomness hidden :=
  let offsets := offsetsFromTail hidden free.offsets
  { offsets
    randomizers := free.randomizers
    chainMasks := fun index => chainMasksFromFree (free.chainMasks index)
    tableMasks := fun index kind =>
      (tableMaskFromFree
        ((mapHidden hidden offsets free.randomizers
          (fun index => chainMasksFromFree (free.chainMasks index)) index).params
          kind).constant
        (free.tableMasks index kind)).1
    tableMasks_sum := fun index kind =>
      (tableMaskFromFree
        ((mapHidden hidden offsets free.randomizers
          (fun index => chainMasksFromFree (free.chainMasks index)) index).params
          kind).constant
        (free.tableMasks index kind)).2 }

def freeFromRandomness {hidden : Hidden} (randomness : Randomness hidden) :
    FreeRandomness where
  offsets := tailFromOffsets randomness.offsets
  randomizers := randomness.randomizers
  chainMasks := fun index => chainMasksFree (randomness.chainMasks index)
  tableMasks := fun index kind => tableMaskFree
    (⟨randomness.tableMasks index kind,
      randomness.tableMasks_sum index kind⟩ :
      IdealAffineTable.MaskFiber
        ((mapHidden hidden randomness.offsets randomness.randomizers
          randomness.chainMasks index).params kind).constant)

@[simp] theorem freeFromRandomness_randomnessFromFree (hidden : Hidden)
    (free : FreeRandomness) :
    freeFromRandomness (randomnessFromFree hidden free) = free := by
  apply FreeRandomness.ext
  · exact (offsetsEquiv hidden).left_inv free.offsets
  · rfl
  · funext index
    exact chainMasksFree_fromFree _
  · funext index kind
    exact tableMaskFree_fromFree _ _

theorem randomnessFromFree_freeFromRandomness (hidden : Hidden)
    (randomness : Randomness hidden) :
    randomnessFromFree hidden (freeFromRandomness randomness) = randomness := by
  apply Randomness.ext
  · exact (offsetsEquiv hidden).right_inv randomness.offsets
  · rfl
  · funext index
    exact chainMasksFromFree_free _
  · funext index kind
    have hoffsets := (offsetsEquiv hidden).right_inv randomness.offsets
    dsimp only [freeFromRandomness]
    change (tableMaskFromFree _ (tableMaskFree
      (⟨randomness.tableMasks index kind,
        randomness.tableMasks_sum index kind⟩ :
        IdealAffineTable.MaskFiber _))).1 = randomness.tableMasks index kind
    rw [show offsetsFromTail hidden (tailFromOffsets randomness.offsets) =
      randomness.offsets from hoffsets]
    exact congrArg Subtype.val (tableMaskFromFree_free
      (⟨randomness.tableMasks index kind,
        randomness.tableMasks_sum index kind⟩ :
        IdealAffineTable.MaskFiber _))

def freeRandomnessEquiv (hidden : Hidden) :
    FreeRandomness ≃ Randomness hidden where
  toFun := randomnessFromFree hidden
  invFun := freeFromRandomness
  left_inv := freeFromRandomness_randomnessFromFree hidden
  right_inv := randomnessFromFree_freeFromRandomness hidden

def freeFromOracle (oracle : InternalOracle) : FreeRandomness where
  offsets := ⟨sampledOffsetTail oracle, sampledOffsetTail_length oracle⟩
  randomizers := fun index =>
    randomizerSample oracle (randomizerPurpose index)
  chainMasks := fun index slot =>
    wordSample oracle (chainPurpose index slot)
  tableMasks := fun index kind slot =>
    CompactScheme.tableMaskFree oracle index kind slot

theorem randomnessFromFree_freeFromOracle (hidden : Hidden)
    (oracle : InternalOracle) :
    randomnessFromFree hidden (freeFromOracle oracle) =
      randomnessFromOracle hidden oracle := by
  apply Randomness.ext
  · rfl
  · rfl
  · funext index
    apply ProjectiveMap.ChainMasks.ext <;> rfl
  · rfl

abbrev RawCoordinate := OracleCoordinate

private theorem scalarFits : scalarFieldModulus ≤ 2 ^ 3072 := by
  calc
    scalarFieldModulus ≤ 2 ^ 256 := by norm_num [scalarFieldModulus]
    _ ≤ 2 ^ 3072 := pow_le_pow_right' (by decide) (by decide)

private theorem baseFits : baseFieldModulus ≤ 2 ^ 3072 := by
  calc
    baseFieldModulus ≤ 2 ^ 256 := by norm_num [baseFieldModulus]
    _ ≤ 2 ^ 3072 := pow_le_pow_right' (by decide) (by decide)

private theorem unitsPositive : 0 < baseFieldModulus - 1 := by
  norm_num [baseFieldModulus]

private theorem unitsFits : baseFieldModulus - 1 ≤ 2 ^ 3072 := by
  calc
    baseFieldModulus - 1 ≤ 2 ^ 256 := by norm_num [baseFieldModulus]
    _ ≤ 2 ^ 3072 := pow_le_pow_right' (by decide) (by decide)

def rawModulus : RawCoordinate → SamplingModulus
  | .offset _ => ⟨scalarFieldModulus, by norm_num [scalarFieldModulus], scalarFits⟩
  | .randomizer _ => ⟨baseFieldModulus - 1, unitsPositive, unitsFits⟩
  | .chain _ _ | .table _ _ _ =>
      ⟨baseFieldModulus, by norm_num [baseFieldModulus], baseFits⟩

def rawPurpose : RawCoordinate → Purpose
  | coordinate => oraclePurpose coordinate

def rawAddress (coordinate : RawCoordinate) : InternalAddress :=
  ⟨rawModulus coordinate, rawPurpose coordinate⟩

theorem rawPurpose_injective : Function.Injective rawPurpose := by
  exact oraclePurpose_injective

theorem rawAddress_injective : Function.Injective rawAddress := by
  intro left right hequal
  apply rawPurpose_injective
  exact congrArg Sigma.snd hequal

abbrev RawValues := (coordinate : RawCoordinate) → Fin (rawModulus coordinate).value

instance (coordinate : RawCoordinate) :
    Nonempty (Fin (rawModulus coordinate).value) :=
  ⟨⟨0, (rawModulus coordinate).positive⟩⟩

def rawFromOracle (oracle : InternalOracle) : RawValues :=
  fun coordinate => oracle (rawModulus coordinate) (rawPurpose coordinate)

noncomputable def wordEquiv : Fin baseFieldModulus ≃ BN254.Fq where
  toFun value := (value.val : ZMod baseFieldModulus)
  invFun value := ⟨value.val, value.val_lt⟩
  left_inv value := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt value.isLt
  right_inv value := by
    exact ZMod.natCast_zmod_val value

@[simp] theorem wordEquiv_val (value : Fin baseFieldModulus) :
    (wordEquiv value).val = value.val := by
  change ((value.val : ZMod baseFieldModulus)).val = value.val
  exact ZMod.val_natCast_of_lt value.isLt

theorem wordSample_val (oracle : InternalOracle) (purpose : Purpose) :
    (wordSample oracle purpose).val =
      (oracle.sample baseFieldModulus (by norm_num [baseFieldModulus])
        baseFits purpose).val := by
  let sampled := oracle.sample baseFieldModulus
    (by norm_num [baseFieldModulus]) baseFits purpose
  unfold wordSample
  change ((sampled.val : Word).val) = sampled.val
  exact ZMod.val_natCast_of_lt sampled.isLt

noncomputable def freeFromRaw (raw : RawValues) : FreeRandomness where
  offsets := offsetTailEquiv (fun index => generatorEquiv
    (Fin.cast (by simp [rawModulus]) (raw (.offset index))))
  randomizers := fun index => unitEquiv
    (Fin.cast (by simp [rawModulus]) (raw (.randomizer index)))
  chainMasks := fun index slot => wordEquiv
    (Fin.cast (by simp [rawModulus]) (raw (.chain index slot)))
  tableMasks := fun index kind slot => wordEquiv
    (Fin.cast (by simp [rawModulus]) (raw (.table index kind slot)))

noncomputable def rawFromFree (free : FreeRandomness) : RawValues
  | .offset index => Fin.cast (by simp [rawModulus])
      (generatorEquiv.symm
        (show BN254.G1 from offsetTailEquiv.symm free.offsets index))
  | .randomizer index => Fin.cast (by simp [rawModulus])
      (unitEquiv.symm (free.randomizers index))
  | .chain index slot => Fin.cast (by simp [rawModulus])
      (wordEquiv.symm (free.chainMasks index slot))
  | .table index kind slot => Fin.cast (by simp [rawModulus])
      (wordEquiv.symm (free.tableMasks index kind slot))

@[simp] theorem rawFromFree_freeFromRaw (raw : RawValues) :
    rawFromFree (freeFromRaw raw) = raw := by
  funext coordinate
  cases coordinate with
  | offset index =>
      have hmod : scalarFieldModulus =
          (rawModulus (.offset index)).value := by simp [rawModulus]
      let value : Fin scalarFieldModulus :=
        Fin.cast (by simp [rawModulus]) (raw (.offset index))
      have htail : offsetTailEquiv.symm
          (offsetTailEquiv (fun index => generatorEquiv
            (Fin.cast (by simp [rawModulus]) (raw (.offset index))))) index =
          generatorEquiv value := by
        exact congrFun (offsetTailEquiv.symm_apply_apply _) index
      change Fin.cast hmod (generatorEquiv.symm
        (offsetTailEquiv.symm (offsetTailEquiv _) index)) = _
      rw [htail, generatorEquiv.symm_apply_apply]
      exact Fin.ext rfl
  | randomizer index =>
      have hmod : baseFieldModulus - 1 =
          (rawModulus (.randomizer index)).value := by simp [rawModulus]
      change Fin.cast hmod (unitEquiv.symm
        (unitEquiv (Fin.cast hmod.symm _))) = _
      rw [unitEquiv.symm_apply_apply]
      exact Fin.ext rfl
  | chain index slot =>
      have hmod : baseFieldModulus =
          (rawModulus (.chain index slot)).value := by simp [rawModulus]
      change Fin.cast hmod (wordEquiv.symm
        (wordEquiv (Fin.cast hmod.symm _))) = _
      rw [wordEquiv.symm_apply_apply]
      exact Fin.ext rfl
  | table index kind slot =>
      have hmod : baseFieldModulus =
          (rawModulus (.table index kind slot)).value := by simp [rawModulus]
      change Fin.cast hmod (wordEquiv.symm
        (wordEquiv (Fin.cast hmod.symm _))) = _
      rw [wordEquiv.symm_apply_apply]
      exact Fin.ext rfl

@[simp] theorem freeFromRaw_rawFromFree (free : FreeRandomness) :
    freeFromRaw (rawFromFree free) = free := by
  apply FreeRandomness.ext
  · rw [← offsetTailEquiv.apply_symm_apply free.offsets]
    apply congrArg offsetTailEquiv
    funext index
    have hmod : scalarFieldModulus =
        (rawModulus (.offset index)).value := by simp [rawModulus]
    change generatorEquiv (Fin.cast hmod.symm (Fin.cast hmod
      (generatorEquiv.symm (offsetTailEquiv.symm free.offsets index)))) = _
    have hcast : Fin.cast hmod.symm (Fin.cast hmod
        (generatorEquiv.symm (offsetTailEquiv.symm free.offsets index))) =
        generatorEquiv.symm (offsetTailEquiv.symm free.offsets index) :=
      Fin.ext rfl
    rw [hcast]
    exact generatorEquiv.apply_symm_apply
      (show BN254.G1 from offsetTailEquiv.symm free.offsets index)
  · funext index
    exact unitEquiv.apply_symm_apply (free.randomizers index)
  · funext index slot
    exact wordEquiv.apply_symm_apply (free.chainMasks index slot)
  · funext index kind slot
    exact wordEquiv.apply_symm_apply (free.tableMasks index kind slot)

noncomputable def rawFreeEquiv : RawValues ≃ FreeRandomness where
  toFun := freeFromRaw
  invFun := rawFromFree
  left_inv := rawFromFree_freeFromRaw
  right_inv := freeFromRaw_rawFromFree

noncomputable def rawRandomnessEquiv (hidden : Hidden) :
    RawValues ≃ Randomness hidden :=
  rawFreeEquiv.trans (freeRandomnessEquiv hidden)

set_option maxRecDepth 4096 in
theorem freeFromRaw_rawFromOracle (oracle : InternalOracle) :
    freeFromRaw (rawFromOracle oracle) = freeFromOracle oracle := by
  apply FreeRandomness.ext
  · apply Subtype.ext
    change List.ofFn (fun index => generatorEquiv (Fin.cast _
      (oracle (rawModulus (.offset index)) (rawPurpose (.offset index))))) =
      sampledOffsetTail oracle
    rw [List.ofFn_eq_map]
    unfold sampledOffsetTail
    apply List.map_congr_left
    intro index hindex
    apply congrArg (fun scalar : Fin scalarFieldModulus =>
      scalar.val • standardGenerator)
    apply Fin.ext
    rfl
  · funext index
    apply Units.ext
    apply ZMod.val_injective
    rfl
  · funext index slot
    dsimp only [freeFromRaw, rawFromOracle, freeFromOracle]
    apply ZMod.val_injective
    rw [wordEquiv_val]
    rw [wordSample_val]
    change (Fin.cast _
      (oracle (rawModulus (.chain index slot))
        (rawPurpose (.chain index slot)))).val =
      (oracle.sample baseFieldModulus (by norm_num [baseFieldModulus])
        baseFits (chainPurpose index slot)).val
    rfl
  · funext index kind slot
    dsimp only [freeFromRaw, rawFromOracle, freeFromOracle]
    apply ZMod.val_injective
    rw [wordEquiv_val]
    rw [show CompactScheme.tableMaskFree oracle index kind slot =
        wordSample oracle (tableMaskPurpose index kind slot) by rfl]
    rw [wordSample_val]
    change (Fin.cast _
      (oracle (rawModulus (.table index kind slot))
        (rawPurpose (.table index kind slot)))).val =
      (oracle.sample baseFieldModulus (by norm_num [baseFieldModulus])
        baseFits (tableMaskPurpose index kind slot)).val
    rfl

theorem rawFromOracle_coordinate_measurable (coordinate : RawCoordinate) :
    Measurable (fun oracle : InternalOracle => rawFromOracle oracle coordinate) := by
  exact (internalOracleLaw_uniform_marginal
    (rawModulus coordinate) (rawPurpose coordinate)).measurable

theorem rawFromOracle_measurable : Measurable rawFromOracle := by
  apply measurable_pi_lambda
  intro coordinate
  exact rawFromOracle_coordinate_measurable coordinate

theorem rawFromOracle_independent :
    iIndepFun
      (fun coordinate : RawCoordinate => fun oracle : InternalOracle =>
        rawFromOracle oracle coordinate)
      internalOracleLaw := by
  exact internalCoordinates_independent.precomp rawAddress_injective

theorem rawFromOracle_law :
    Measure.map rawFromOracle internalOracleLaw =
      uniformOn (Set.univ : Set RawValues) := by
  have hindependent := rawFromOracle_independent.map_fun_eq_infinitePi_map
    rawFromOracle_coordinate_measurable
  change Measure.map rawFromOracle internalOracleLaw = _ at hindependent
  rw [hindependent]
  have hmarginals :
      (fun coordinate : RawCoordinate =>
        Measure.map (fun oracle : InternalOracle => rawFromOracle oracle coordinate)
          internalOracleLaw) =
      (fun coordinate : RawCoordinate => internalValueLaw (rawModulus coordinate)) := by
    funext coordinate
    exact (internalOracleLaw_uniform_marginal
      (rawModulus coordinate) (rawPurpose coordinate)).map_eq
  rw [hmarginals]
  exact infinitePi_uniform_univ_dependent
    (fun coordinate : RawCoordinate => Fin (rawModulus coordinate).value)

theorem rawRandomnessEquiv_rawFromOracle (hidden : Hidden)
    (oracle : InternalOracle) :
    rawRandomnessEquiv hidden (rawFromOracle oracle) =
      randomnessFromOracle hidden oracle := by
  change randomnessFromFree hidden (freeFromRaw (rawFromOracle oracle)) = _
  rw [freeFromRaw_rawFromOracle]
  exact randomnessFromFree_freeFromOracle hidden oracle

noncomputable instance (hidden : Hidden) :
    Finite (Randomness hidden) :=
  Finite.of_injective (rawRandomnessEquiv hidden).symm
    (rawRandomnessEquiv hidden).symm.injective

noncomputable instance (hidden : Hidden) :
    IsProbabilityMeasure (randomnessLaw hidden) := by
  change IsProbabilityMeasure
    (uniformOn Set.univ : Measure (Randomness hidden))
  exact isProbabilityMeasure_uniformOn Set.finite_univ Set.univ_nonempty

set_option maxRecDepth 4096 in
theorem randomnessFromOracle_measurable (hidden : Hidden) :
    Measurable (randomnessFromOracle hidden) := by
  rw [show randomnessFromOracle hidden =
      (rawRandomnessEquiv hidden) ∘ rawFromOracle by
    funext oracle
    exact rawRandomnessEquiv_rawFromOracle hidden oracle]
  exact Measurable.of_discrete.comp rawFromOracle_measurable

set_option maxRecDepth 4096 in
theorem randomnessFromOracle_law (hidden : Hidden) :
    Measure.map (randomnessFromOracle hidden) internalOracleLaw =
      randomnessLaw hidden := by
  rw [show randomnessFromOracle hidden =
      (rawRandomnessEquiv hidden) ∘ rawFromOracle by
    funext oracle
    exact rawRandomnessEquiv_rawFromOracle hidden oracle]
  rw [← Measure.map_map Measurable.of_discrete rawFromOracle_measurable]
  rw [rawFromOracle_law]
  exact (measurePreserving_uniformOfFiniteEquiv
    (rawRandomnessEquiv hidden)).map_eq

end GarblingPrize.Submission.CompactOracleLaw
