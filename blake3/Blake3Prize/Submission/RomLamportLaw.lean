import Blake3Prize.Submission.RomLamportGuessing
import Mathlib.Data.Fintype.EquivFin

/-! Disintegrating the protected uniform distinct-pair key distribution.
The auxiliary ranks are independent of selected labels; decoding a rank
gives a uniform opposite label, never the already disclosed label. -/
namespace Blake3Prize.Submission.RomLamportLaw
open SecretRelease MeasureTheory ProbabilityTheory RomLamportGuessing

abbrev Rank := Fin (2^256-1)
instance : Nonempty Rank := ⟨⟨0, by norm_num⟩⟩

noncomputable def complementEquiv (active : Label) : Complement active ≃ Rank := by
  letI := Fintype.ofFinite (Complement active)
  exact Fintype.equivFinOfCardEq (by simpa only [Nat.card_eq_fintype_card] using complement_card active)

noncomputable def pairEquiv (bit : Bool) : Pair ≃ Label × Rank :=
  (selectedPairEquiv bit).trans (Equiv.sigmaEquivProdOfEquiv complementEquiv)

@[simp] theorem pairEquiv_active (bit : Bool) (pair : Pair) :
    (pairEquiv bit pair).1 = pair.get bit := rfl

@[simp] theorem pairEquiv_opposite (bit : Bool) (pair : Pair) :
    ((complementEquiv (pair.get bit)).symm (pairEquiv bit pair).2).val = pair.get (!bit) := by
  change ((complementEquiv (pair.get bit)).symm
    (complementEquiv (pair.get bit) ⟨pair.get (!bit), _⟩)).val = _
  rw [Equiv.symm_apply_apply]

noncomputable def keysEquiv {ι : Type*} (bits : ι → Bool) :
    (ι → Pair) ≃ (ι → Label) × (ι → Rank) where
  toFun keys := (fun i => (pairEquiv (bits i) (keys i)).1,
    fun i => (pairEquiv (bits i) (keys i)).2)
  invFun split := fun i => (pairEquiv (bits i)).symm (split.1 i,split.2 i)
  left_inv keys := by funext i; exact (pairEquiv (bits i)).symm_apply_apply (keys i)
  right_inv split := by
    apply Prod.ext <;> funext i
    · exact congrArg Prod.fst ((pairEquiv (bits i)).apply_symm_apply (split.1 i,split.2 i))
    · exact congrArg Prod.snd ((pairEquiv (bits i)).apply_symm_apply (split.1 i,split.2 i))

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

theorem keysEquiv_preserving {ι : Type*} [Fintype ι] (bits : ι → Bool) :
    MeasurePreserving (keysEquiv bits)
      (uniformOn (Set.univ : Set (ι → Pair)))
      ((uniformOn (Set.univ : Set (ι → Label))).prod
        (uniformOn (Set.univ : Set (ι → Rank)))) := by
  rw [prod_uniform_univ]
  exact RomFiniteProbability.uniform_equiv (keysEquiv bits)

noncomputable def hiddenFromRanks {ι : Type*} (active : ι → Label) (ranks : ι → Rank) :
    HiddenKeys active := fun i => (complementEquiv (active i)).symm (ranks i)

theorem hiddenFromRanks_preserving {ι : Type*} [Fintype ι] (active : ι → Label) :
    MeasurePreserving (hiddenFromRanks active)
      (uniformOn (Set.univ : Set (ι → Rank))) (hiddenLaw active) := by
  have hpi : Measure.infinitePi (fun _ : ι => uniformOn (Set.univ : Set Rank)) =
      uniformOn (Set.univ : Set (ι → Rank)) := by
    rw [Measure.infinitePi_eq_pi, ← uniformOn_pi (f := fun _ : ι => (Set.univ : Set Rank))]
    simp
  refine ⟨Measurable.of_discrete, ?_⟩
  unfold hiddenFromRanks
  rw [← hpi, Measure.infinitePi_map_pi _ (fun _ => Measurable.of_discrete)]
  unfold hiddenLaw
  congr 1
  funext i
  exact (RomFiniteProbability.uniform_equiv (complementEquiv (active i)).symm).map_eq

@[simp] theorem hiddenFromRanks_keysEquiv {ι : Type*} (bits : ι → Bool)
    (keys : ι → Pair) (i : ι) :
    (hiddenFromRanks (keysEquiv bits keys).1 (keysEquiv bits keys).2 i).val =
      (keys i).get (!(bits i)) :=
  pairEquiv_opposite (bits i) (keys i)

end Blake3Prize.Submission.RomLamportLaw
