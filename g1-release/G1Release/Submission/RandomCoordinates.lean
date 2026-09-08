import G1Release.Submission.BoundaryFacts
import G1Release.Submission.SamplingEquivalences

namespace G1Release.Submission.Randomized
open GarblingPrize.Protected G1Release.Protected
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

inductive OracleCoordinate where
  | offset (index : Fin 160)
  | randomizer (index : Fin 161)
  | chain (index : Fin 161) (slot : Fin 8)
  | table (index : Fin 161) (kind : ProjectiveMap.TableKind)
      (slot : Fin 253)
  deriving DecidableEq, Fintype

/-- A deterministic, injective purpose assignment internal to this
submission.  It identifies coordinates within one Compact artifact only. -/
def coordinateIndex : OracleCoordinate → Nat
  | .offset index => index.val
  | .randomizer index => 160 + index.val
  | .chain index slot => 321 + 8 * index.val + slot.val
  | .table index kind slot =>
      1609 + (11 * index.val + kind.index) * 253 + slot.val

private theorem tableKind_index_injective :
    Function.Injective ProjectiveMap.TableKind.index := by
  intro left right hequal
  cases left <;> cases right <;>
    simp only [ProjectiveMap.TableKind.index] at hequal ⊢ <;> omega

theorem coordinateIndex_injective : Function.Injective coordinateIndex := by
  intro left right hequal
  cases left with
  | offset leftIndex =>
      cases right with
      | offset rightIndex =>
          change leftIndex.val = rightIndex.val at hequal
          congr; exact Fin.ext hequal
      | randomizer rightIndex =>
          change leftIndex.val = 160 + rightIndex.val at hequal
          omega
      | chain rightIndex rightSlot =>
          change leftIndex.val = 321 + 8 * rightIndex.val + rightSlot.val at hequal
          omega
      | table rightIndex rightKind rightSlot =>
          change leftIndex.val = 1609 +
            (11 * rightIndex.val + rightKind.index) * 253 + rightSlot.val at hequal
          omega
  | randomizer leftIndex =>
      cases right with
      | offset rightIndex =>
          change 160 + leftIndex.val = rightIndex.val at hequal
          omega
      | randomizer rightIndex =>
          change 160 + leftIndex.val = 160 + rightIndex.val at hequal
          congr; apply Fin.ext; omega
      | chain rightIndex rightSlot =>
          change 160 + leftIndex.val =
            321 + 8 * rightIndex.val + rightSlot.val at hequal
          omega
      | table rightIndex rightKind rightSlot =>
          change 160 + leftIndex.val = 1609 +
            (11 * rightIndex.val + rightKind.index) * 253 + rightSlot.val at hequal
          omega
  | chain leftIndex leftSlot =>
      cases right with
      | offset rightIndex =>
          change 321 + 8 * leftIndex.val + leftSlot.val = rightIndex.val at hequal
          omega
      | randomizer rightIndex =>
          change 321 + 8 * leftIndex.val + leftSlot.val =
            160 + rightIndex.val at hequal
          omega
      | chain rightIndex rightSlot =>
          change 321 + 8 * leftIndex.val + leftSlot.val =
            321 + 8 * rightIndex.val + rightSlot.val at hequal
          have hindex : leftIndex.val = rightIndex.val := by omega
          have hslot : leftSlot.val = rightSlot.val := by omega
          congr <;> apply Fin.ext <;> assumption
      | table rightIndex rightKind rightSlot =>
          change 321 + 8 * leftIndex.val + leftSlot.val = 1609 +
            (11 * rightIndex.val + rightKind.index) * 253 + rightSlot.val at hequal
          omega
  | table leftIndex leftKind leftSlot =>
      cases right with
      | offset rightIndex =>
          change 1609 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = rightIndex.val at hequal
          omega
      | randomizer rightIndex =>
          change 1609 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = 160 + rightIndex.val at hequal
          omega
      | chain rightIndex rightSlot =>
          change 1609 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = 321 + 8 * rightIndex.val + rightSlot.val at hequal
          omega
      | table rightIndex rightKind rightSlot =>
          change 1609 + (11 * leftIndex.val + leftKind.index) * 253 +
            leftSlot.val = 1609 +
              (11 * rightIndex.val + rightKind.index) * 253 +
                rightSlot.val at hequal
          have howner : 11 * leftIndex.val + leftKind.index =
              11 * rightIndex.val + rightKind.index := by omega
          have hslot : leftSlot.val = rightSlot.val := by omega
          have hindex : leftIndex.val = rightIndex.val := by
            have hleft : leftKind.index < 11 := by cases leftKind <;> decide
            have hright : rightKind.index < 11 := by cases rightKind <;> decide
            omega
          have hkindIndex : leftKind.index = rightKind.index := by omega
          have hkind : leftKind = rightKind :=
            tableKind_index_injective hkindIndex
          congr
          · exact Fin.ext hindex
          · exact Fin.ext hslot


def rawModulus : OracleCoordinate → Nat
  | .offset _ => scalarFieldModulus
  | .randomizer _ => baseFieldModulus - 1
  | .chain _ _ | .table _ _ _ => baseFieldModulus

theorem rawModulus_pos (i : OracleCoordinate) : 0 < rawModulus i := by
  cases i <;> norm_num [rawModulus, baseFieldModulus, BoundaryFacts.scalar_modulus]

abbrev RawValues := (i : OracleCoordinate) → Fin (rawModulus i)

instance (i : OracleCoordinate) : Nonempty (Fin (rawModulus i)) :=
  ⟨⟨0, rawModulus_pos i⟩⟩

noncomputable def freeFromRaw (raw : RawValues) : FreeRandomness where
  offsets := offsetTailEquiv (fun index => generatorEquiv
    (Fin.cast (by simp [rawModulus]) (raw (.offset index))))
  scales := fun index => unitEquiv
    (Fin.cast (by simp [rawModulus]) (raw (.randomizer index)))
  chains := fun index slot => wordEquiv
    (Fin.cast (by simp [rawModulus]) (raw (.chain index slot)))
  tableMasks := fun index kind slot => wordEquiv
    (Fin.cast (by simp [rawModulus]) (raw (.table index kind slot)))

noncomputable def rawFromFree (free : FreeRandomness) : RawValues
  | .offset index => Fin.cast (by simp [rawModulus])
      (generatorEquiv.symm
        (show BN254.G1 from offsetTailEquiv.symm free.offsets index))
  | .randomizer index => Fin.cast (by simp [rawModulus])
      (unitEquiv.symm (free.scales index))
  | .chain index slot => Fin.cast (by simp [rawModulus])
      (wordEquiv.symm (free.chains index slot))
  | .table index kind slot => Fin.cast (by simp [rawModulus])
      (wordEquiv.symm (free.tableMasks index kind slot))

@[simp] theorem rawFromFree_freeFromRaw (raw : RawValues) :
    rawFromFree (freeFromRaw raw) = raw := by
  funext coordinate
  cases coordinate with
  | offset index =>
      have hmod : scalarFieldModulus =
          (rawModulus (.offset index)) := by simp [rawModulus]
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
          (rawModulus (.randomizer index)) := by simp [rawModulus]
      change Fin.cast hmod (unitEquiv.symm
        (unitEquiv (Fin.cast hmod.symm _))) = _
      rw [unitEquiv.symm_apply_apply]
      exact Fin.ext rfl
  | chain index slot =>
      have hmod : baseFieldModulus =
          (rawModulus (.chain index slot)) := by simp [rawModulus]
      change Fin.cast hmod (wordEquiv.symm
        (wordEquiv (Fin.cast hmod.symm _))) = _
      rw [wordEquiv.symm_apply_apply]
      exact Fin.ext rfl
  | table index kind slot =>
      have hmod : baseFieldModulus =
          (rawModulus (.table index kind slot)) := by simp [rawModulus]
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
        (rawModulus (.offset index)) := by simp [rawModulus]
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
    exact unitEquiv.apply_symm_apply (free.scales index)
  · funext index slot
    exact wordEquiv.apply_symm_apply (free.chains index slot)
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


end G1Release.Submission.Randomized
