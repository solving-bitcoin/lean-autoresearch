import WotsLamport.Submission.ChainPartitionLaw

namespace WotsLamport.Submission
open SecretRelease

/-- A finite family of programmed cells; all other oracle cells retain the
baseline answer. This is a mathematical table operation, not native code. -/
noncomputable def overlayOracle {I D R : Type} (address : I → D) (answer : I → R)
    (baseline : D → R) (input : D) : R := by
  classical
  exact if found : ∃ i, address i = input then answer (Classical.choose found)
    else baseline input

theorem overlayOracle_at {I D R : Type} (address : I → D) (answer : I → R)
    (baseline : D → R) (injective : Function.Injective address) (i : I) :
    overlayOracle address answer baseline (address i) = answer i := by
  classical
  have found : ∃ j, address j = address i := ⟨i,rfl⟩
  rw [overlayOracle, dif_pos found]
  exact congrArg answer (injective (Classical.choose_spec found))

theorem overlayOracle_off {I D R : Type} (address : I → D) (answer : I → R)
    (baseline : D → R) (input : D) (missing : ∀ i, address i ≠ input) :
    overlayOracle address answer baseline input = baseline input := by
  have hn : ¬∃ i, address i = input := by rintro ⟨i,hi⟩; exact missing i hi
  simp only [overlayOracle, dif_neg hn]

theorem overlayOracle_restore {I D R : Type} (address : I → D)
    (injective : Function.Injective address) (fixed : D → R) (fill : I → R) :
    overlayOracle address (fixed ∘ address) (overlayOracle address fill fixed) = fixed := by
  classical
  funext input
  by_cases found : ∃ i, address i = input
  · obtain ⟨i,rfl⟩ := found
    exact overlayOracle_at address _ _ injective i
  · have missing : ∀ i, address i ≠ input := by intro i hi; exact found ⟨i,hi⟩
    rw [overlayOracle_off address _ _ input missing,
      overlayOracle_off address _ _ input missing]

/-- A prescribed oracle has exactly one free answer per overwritten cell in
its overlay fiber. This remains valid when the address family was obtained
from other fixed sampled data, as long as its injectivity is established. -/
noncomputable def overlayFiberEquiv {I D R : Type} (address : I → D)
    (injective : Function.Injective address) (fixed : D → R) :
    {baseline : D → R // overlayOracle address (fixed ∘ address) baseline = fixed} ≃
      (I → R) := by
  classical
  exact {
    toFun baseline i := baseline.val (address i)
    invFun fill := ⟨overlayOracle address fill fixed,
      overlayOracle_restore address injective fixed fill⟩
    left_inv baseline := by
      apply Subtype.ext
      funext input
      by_cases found : ∃ i, address i = input
      · obtain ⟨i,rfl⟩ := found
        exact overlayOracle_at address _ fixed injective i
      · have missing : ∀ i, address i ≠ input := by intro i hi; exact found ⟨i,hi⟩
        rw [overlayOracle_off address _ fixed input missing]
        have he := congrFun baseline.property input
        rw [overlayOracle_off address _ baseline.val input missing] at he
        exact he.symm
    right_inv fill := by
      funext i
      exact overlayOracle_at address fill fixed injective i }

theorem overlay_fiber_card {I D R : Type} [Fintype I] [Fintype R]
    (address : I → D) (injective : Function.Injective address) (fixed : D → R) :
    Nat.card {baseline : D → R // overlayOracle address (fixed ∘ address) baseline = fixed} =
      Fintype.card R ^ Fintype.card I := by
  classical
  rw [Nat.card_congr (overlayFiberEquiv address injective fixed),
    Nat.card_eq_fintype_card, Fintype.card_fun]

theorem programChainOracle_eq_overlay (baseline : Hash) (tape : ChainTape) :
    programChainOracle baseline tape =
      overlayOracle (fun edge : ChainEdge => ByteArray.mk (tape edge.val).toArray)
        (fun edge => tape (edgeNext edge)) baseline := rfl

theorem chain_address_injective (tape : ChainTape) (distinct : Function.Injective tape) :
    Function.Injective (fun edge : ChainEdge => ByteArray.mk (tape edge.val).toArray) := by
  intro a b he
  apply Subtype.ext
  exact distinct (Vector.toArray_inj.mp (congrArg ByteArray.data he))

theorem consistent_tape_unique (fixed : Hash) (keys : WotsLamport.Protected.Keys)
    (tape : ChainTape) (initial : tapeKeys tape = keys) (consistent : TapeConsistent fixed tape) :
    tape = actualChainTape fixed keys := by
  rw [← initial]
  funext position
  exact (chain_tape fixed tape consistent position.1 position.2.val
    (Nat.le_of_lt_succ position.2.isLt)).symm

/-- A collision-free consistent tape fixes 989 distinct oracle cells. Exactly
989 arbitrary old answers are forgotten by programming those cells, including
when the full oracle input space is infinite. This is a fiber count, not yet
a normalized probability or real/ideal distribution theorem. -/
theorem chain_programming_fiber_card (tape : ChainTape) (distinct : Function.Injective tape)
    (fixed : Hash) (consistent : TapeConsistent fixed tape) :
    Nat.card {baseline : Hash // programChainOracle baseline tape = fixed} =
      (2^256)^989 := by
  classical
  letI := Fintype.ofFinite Label
  let address := fun edge : ChainEdge => ByteArray.mk (tape edge.val).toArray
  have ha : fixed ∘ address = fun edge => tape (edgeNext edge) := by
    funext edge
    exact consistent edge
  have hlabel : Fintype.card Label = 2^256 := by rw [bytes_card]; norm_num
  have h := overlay_fiber_card address (chain_address_injective tape distinct) fixed
  simpa only [ha, programChainOracle_eq_overlay, chainEdge_card, hlabel, address] using h


/-- The full programming map retains the keys and programmed oracle together.
Restricting its source to collision-free tapes prevents inconsistent edge
assignments from entering the fiber. -/
abbrev ChainProgramFiber (keys : WotsLamport.Protected.Keys) (fixed : Hash) :=
  {sample : ChainTape × Hash // Function.Injective sample.1 ∧
    tapeKeys sample.1 = keys ∧ programChainOracle sample.2 sample.1 = fixed}

theorem chain_program_fiber_tape (keys : WotsLamport.Protected.Keys) (fixed : Hash)
    (sample : ChainProgramFiber keys fixed) : sample.val.1 = actualChainTape fixed keys := by
  have consistent := programChainOracle_consistent sample.val.2 sample.val.1 sample.property.1
  rw [sample.property.2.2] at consistent
  exact consistent_tape_unique fixed keys sample.val.1 sample.property.2.1 consistent

/-- For a collision-free real chain table, the only ideal tape in a joint
key/oracle fiber is the actual chain tape. The remaining freedom is exactly
the old oracle answers overwritten by the 989 edges. -/
noncomputable def chainProgramFiberEquiv (keys : WotsLamport.Protected.Keys)
    (fixed : Hash) (distinct : Function.Injective (actualChainTape fixed keys)) :
    ChainProgramFiber keys fixed ≃
      {baseline : Hash // programChainOracle baseline (actualChainTape fixed keys) = fixed} where
  toFun sample := ⟨sample.val.2, by
    rw [← chain_program_fiber_tape keys fixed sample]
    exact sample.property.2.2⟩
  invFun baseline := ⟨(actualChainTape fixed keys, baseline.val),
    distinct, rfl, baseline.property⟩
  left_inv sample := by
    apply Subtype.ext
    exact Prod.ext (chain_program_fiber_tape keys fixed sample).symm rfl
  right_inv baseline := by
    apply Subtype.ext
    rfl

theorem chain_program_joint_fiber_card (keys : WotsLamport.Protected.Keys)
    (fixed : Hash) (distinct : Function.Injective (actualChainTape fixed keys)) :
    Nat.card (ChainProgramFiber keys fixed) = (2^256)^989 := by
  rw [Nat.card_congr (chainProgramFiberEquiv keys fixed distinct)]
  exact chain_programming_fiber_card _ distinct fixed (actualChainTape_consistent fixed keys)

end WotsLamport.Submission
