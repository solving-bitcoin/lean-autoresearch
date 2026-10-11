import WotsLamport.Submission.ChainProgrammingLaw

namespace WotsLamport.Submission
open SecretRelease WotsLamport.Protected MeasureTheory ProbabilityTheory OracleComp

abbrev HiddenChainTape := ChainEdge → Label

/-- Separate the public endpoints from every nonpublic node without dropping
or duplicating a coordinate of the ideal tape. -/
def chainPartitionEquiv : ChainTape ≃ PublicKey × HiddenChainTape where
  toFun tape := (tapePublicKey tape, fun edge => tape edge.val)
  invFun sample position :=
    if hidden : position.2.val < maximum position.1 then sample.2 ⟨position, hidden⟩
    else sample.1 position.1
  left_inv tape := by
    funext position
    rcases position with ⟨j,k⟩
    by_cases hk : k.val < maximum j
    · simp [hk]
    · have he : k = (⟨maximum j, Nat.lt_succ_self _⟩ : Fin (maximum j+1)) :=
        Fin.ext (by change k.val = maximum j; have := k.isLt; omega)
      subst k
      simp [tapePublicKey]
  right_inv sample := by
    apply Prod.ext
    · funext j
      simp [tapePublicKey]
    · funext edge
      simp [edge.property]

theorem chainPartition_hidden (pk : PublicKey) (hidden : HiddenChainTape) (edge : ChainEdge) :
    chainPartitionEquiv.symm (pk,hidden) edge.val = hidden edge := by
  simp [chainPartitionEquiv, edge.property]

theorem uniform_product {A B : Type} [Finite A] [Finite B] [Nonempty A] [Nonempty B]
    [MeasurableSpace A] [MeasurableSpace B]
    [DiscreteMeasurableSpace A] [DiscreteMeasurableSpace B] :
    uniformOn (Set.univ : Set (A × B)) =
      (uniformOn (Set.univ : Set A)).prod (uniformOn (Set.univ : Set B)) := by
  classical
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite B
  apply Measure.ext_of_singleton
  rintro ⟨a,b⟩
  have hp : ((uniformOn (Set.univ : Set A)).prod (uniformOn (Set.univ : Set B))) {(a,b)} =
      uniformOn (Set.univ : Set A) {a} * uniformOn (Set.univ : Set B) {b} := by
    rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  rw [hp]
  simp only [uniformOn_univ, Measure.count_singleton, Fintype.card_prod, Nat.cast_mul, one_div]
  exact ENNReal.mul_inv (Or.inr (by simp)) (Or.inl (by simp))

/-- Exact independence in the ideal tape, including the public endpoints.
No claim about real random-oracle chains is inferred from this partition. -/
theorem uniform_chain_partition :
    (uniformOn (Set.univ : Set ChainTape)).map chainPartitionEquiv =
      (uniformOn (Set.univ : Set PublicKey)).prod
        (uniformOn (Set.univ : Set HiddenChainTape)) := by
  classical
  letI := Fintype.ofFinite Label
  rw [uniform_map_equiv, uniform_product]

def chainEdgePositionEquiv : ChainEdge ≃ ((j : Fin 67) × Fin (maximum j)) where
  toFun edge := ⟨edge.val.1, ⟨edge.val.2.val, edge.property⟩⟩
  invFun position := ⟨⟨position.1, ⟨position.2.val,
    lt_trans position.2.isLt (Nat.lt_succ_self _)⟩⟩, position.2.isLt⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem chainEdge_card : Fintype.card ChainEdge = 989 := by
  rw [Fintype.card_congr chainEdgePositionEquiv, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  decide +kernel

/-- The baseline/program may be chosen after seeing these fixed public
endpoints. They must remain independent of the 989 hidden ideal nodes;
an artifact-dependent program needs the further ciphertext hybrid. -/
theorem ideal_chain_program_difference_public {A : Type} (pk : PublicKey)
    (baseline : Hash) (p : Program A) (q : Nat) (bound : IsTotalQueryBound p q) :
    uniformOn (Set.univ : Set HiddenChainTape)
      {hidden | ROM.run baseline p ≠
        ROM.run (programChainOracle baseline (chainPartitionEquiv.symm (pk,hidden))) p} ≤
          (989 : ENNReal) * q / 2^256 := by
  classical
  letI := Fintype.ofFinite Label
  have hlabel : Fintype.card Label = 2^256 := by rw [bytes_card]; norm_num
  have mass (edge : ChainEdge) (label : Label) :
      uniformOn (Set.univ : Set HiddenChainTape) {hidden | hidden edge = label} ≤
        1/(2 : ENNReal)^256 := by
    simpa only [hlabel, Nat.cast_pow, Nat.cast_ofNat] using
      (uniform_coordinate_mass edge label).le
  have off (hidden : HiddenChainTape) (input : ByteArray)
      (missing : ∀ edge, chainQueryTarget input ≠ some (hidden edge)) :
      baseline input = programChainOracle baseline (chainPartitionEquiv.symm (pk,hidden)) input := by
    apply (programChainOracle_off_tape baseline _ input ?_).symm
    intro edge he
    apply missing edge
    rw [← he, chainPartition_hidden]
    exact chainQueryTarget_complete (hidden edge)
  have h := multi_target_run_difference_bound
    (uniformOn (Set.univ : Set HiddenChainTape)) (fun edge hidden => hidden edge)
    (1/(2 : ENNReal)^256) mass (fun _ => chainQueryTarget) baseline
    (fun hidden => programChainOracle baseline (chainPartitionEquiv.symm (pk,hidden))) off p q bound
  simpa only [chainEdge_card, Nat.cast_ofNat, div_eq_mul_inv, one_mul, mul_assoc] using h

end WotsLamport.Submission
