import GarblingPrize.Submission.IdealAffineTable
import Mathlib.Logic.Equiv.Fin.Rotate

namespace GarblingPrize.Submission.BinaryFieldHint

/-!
An exact randomized conversion from a binary pad to a prime-field mask with
one public hint bit.  This is the prospective row reduction for the 8.2 MB
goal; the ranked candidate is unchanged until its full privacy proof is wired.

Let M = 2p+n, with 0 < n < p.  Regard the M equally likely pad values as edges
of a bipartite graph with p vertices on each side.  There is an identity edge
at every vertex, a shifted edge i -> i+1, and n additional identity edges at
the evenly spaced vertices floor(((k+1)p-1)/n).  The hint chooses an endpoint.

Put e_i = ((i+1)n) mod p and delta_i = [e_i < n].  Using a uniform integer
coin in [0,4p), choose the left endpoint with the following integer thresholds:

  ordinary identity: 2M-4e_i if delta_i=0, M-2e_i otherwise;
  shifted edge:       4e_i;
  additional edge:    M-2e_i.

Each (endpoint, hint) has exactly 2M preimages among the 4pM equally likely
(pad, coin) states.  The endpoint is therefore exactly uniform in Fp and
independent of the public hint.  The private odd-modulus coin is essential:
there is no assertion that a deterministic binary-to-field reduction is uniform.

For BN254 choose M=2^255.  A false row decodes its field mask from 255 bits of
the false label and the public hint.  The true row stores one 254-bit XOR
ciphertext of mask+coefficient*weight.  One field constant per table corrects
the sum of the independently generated masks.  Thus each 254-row table uses
ceil(254*255/8)+32 = 8129 bytes, and 91*11 tables use 8,137,129 bytes.
A simpler byte-aligned layout uses one 32-byte row and one 32-byte constant:
255*32 = 8160 bytes/table, or 8,168,160 bytes overall, still below the goal.

Privacy must preserve the entire active label.  For a selected false row,
keep its pad and coin fixed and translate the unused true pad.  For a selected
true row, translate the decoded mask while preserving the hint, using a
bijection between the equal-size finite fibers.  These row transports must
then be connected to the existing affine, chain-mask, and GLV privacy proofs.
-/

def rangeSize (p n : Nat) : Nat := 2 * p + n

def before (p n i : Nat) : Nat := i * n % p

def phase (p n i : Nat) : Nat := (i + 1) * n % p

def extra (p n i : Nat) : Prop := phase p n i < n

instance (p n i : Nat) : Decidable (extra p n i) := inferInstanceAs
  (Decidable (phase p n i < n))

def identityThreshold (p n i : Nat) : Nat :=
  if extra p n i then rangeSize p n - 2 * phase p n i
  else 2 * rangeSize p n - 4 * phase p n i

def shiftedThreshold (p n i : Nat) : Nat := 4 * phase p n i

def extraThreshold (p n i : Nat) : Nat := rangeSize p n - 2 * phase p n i

def extraIndex (p n k : Nat) : Nat := ((k + 1) * p - 1) / n

def extraRank (p n i : Nat) : Nat := (i + 1) * n / p - 1

theorem before_lt {p n i : Nat} (hp : 0 < p) : before p n i < p :=
  Nat.mod_lt _ hp

theorem phase_lt {p n i : Nat} (hp : 0 < p) : phase p n i < p :=
  Nat.mod_lt _ hp

theorem phase_eq_add_mod (p n i : Nat) :
    phase p n i = (before p n i + n) % p := by
  simp [phase, before, Nat.add_mul, Nat.add_mod]

theorem phase_relation {p n i : Nat} (hp : 0 < p) (hn : n < p) :
    if extra p n i then phase p n i + p = before p n i + n
    else phase p n i = before p n i + n := by
  have hb := before_lt (n := n) (i := i) hp
  have he := phase_lt (n := n) (i := i) hp
  have hm := phase_eq_add_mod p n i
  by_cases hwrap : p ≤ before p n i + n
  · have hsmall : before p n i + n < 2 * p := by omega
    have hquot : (before p n i + n) / p = 1 := by
      apply Nat.div_eq_of_lt_le <;> omega
    have hdiv := Nat.mod_add_div (before p n i + n) p
    rw [← hm, hquot] at hdiv
    have hx : extra p n i := by dsimp [extra]; omega
    simp only [hx, ↓reduceIte]
    omega
  · have hsmall : before p n i + n < p := by omega
    rw [Nat.mod_eq_of_lt hsmall] at hm
    have hx : ¬extra p n i := by dsimp [extra]; omega
    simp only [hx, ↓reduceIte]
    exact hm

theorem identityThreshold_le {p n i : Nat} (hp : 0 < p) (hn : n < p) :
    identityThreshold p n i ≤ 4 * p := by
  have he := phase_lt (n := n) (i := i) hp
  unfold identityThreshold extra rangeSize
  by_cases h : phase p n i < n <;> simp only [h, ↓reduceIte] <;> omega

theorem shiftedThreshold_le {p n i : Nat} (hp : 0 < p) :
    shiftedThreshold p n i ≤ 4 * p := by
  have he := phase_lt (n := n) (i := i) hp
  dsimp [shiftedThreshold]
  omega

theorem extraThreshold_le {p n i : Nat} (hn : n < p) :
    extraThreshold p n i ≤ 4 * p := by
  dsimp [extraThreshold, rangeSize]
  omega

/-- The three possible incoming left-endpoint fibers have total size 2M. -/
theorem left_fiber_balance {p n i : Nat} (hp : 0 < p) (hn : n < p) :
    identityThreshold p n i + shiftedThreshold p n i +
        (if extra p n i then extraThreshold p n i else 0) =
      2 * rangeSize p n := by
  have he := phase_lt (n := n) (i := i) hp
  unfold identityThreshold shiftedThreshold extraThreshold extra rangeSize
  by_cases h : phase p n i < n <;> simp only [h, ↓reduceIte] <;> omega

/-- The shifted right endpoint at i comes from the preceding vertex, whose
phase is `before i`.  Its three incoming fibers again have total size 2M. -/
theorem right_fiber_balance {p n i : Nat} (hp : 0 < p) (hn : n < p) :
    (4 * p - identityThreshold p n i) + (4 * p - 4 * before p n i) +
        (if extra p n i then 4 * p - extraThreshold p n i else 0) =
      2 * rangeSize p n := by
  have he := phase_lt (n := n) (i := i) hp
  have hb := before_lt (n := n) (i := i) hp
  have hr := phase_relation (i := i) hp hn
  unfold identityThreshold extraThreshold rangeSize
  split <;> rename_i h <;> simp only [h, ↓reduceIte] at hr ⊢
  · have hh : phase p n i < n := h
    omega
  · have hh : n ≤ phase p n i := Nat.le_of_not_lt h
    omega

theorem extraIndex_bounds {p n k : Nat} (hp : 0 < p) (hn : 0 < n) :
    extraIndex p n k * n < (k + 1) * p ∧
      (k + 1) * p ≤ (extraIndex p n k + 1) * n := by
  have hpos : 0 < (k + 1) * p := Nat.mul_pos (by omega) hp
  have hmod := Nat.mod_lt ((k + 1) * p - 1) hn
  have hdiv := Nat.mod_add_div ((k + 1) * p - 1) n
  change _ + n * extraIndex p n k = _ at hdiv
  rw [Nat.mul_comm n (extraIndex p n k)] at hdiv
  have hadd : (extraIndex p n k + 1) * n = extraIndex p n k * n + n := by ring
  omega

theorem extraIndex_lt {p n k : Nat} (hp : 0 < p) (hn : 0 < n)
    (hk : k < n) : extraIndex p n k < p := by
  have hb := (extraIndex_bounds (k := k) hp hn).1
  have hle : (k + 1) * p ≤ n * p := Nat.mul_le_mul_right p (by omega)
  have hlt : extraIndex p n k * n < p * n := by nlinarith
  exact Nat.lt_of_mul_lt_mul_right hlt

theorem extraIndex_quotient {p n k : Nat} (hp : 0 < p) (hn : 0 < n)
    (hnp : n < p) : (extraIndex p n k + 1) * n / p = k + 1 := by
  have hb := extraIndex_bounds (k := k) hp hn
  apply Nat.div_eq_of_lt_le <;> nlinarith [hb.1, hb.2]

theorem extraIndex_extra {p n k : Nat} (hp : 0 < p) (hn : 0 < n)
    (hnp : n < p) : extra p n (extraIndex p n k) := by
  have hb := extraIndex_bounds (k := k) hp hn
  have hquot := extraIndex_quotient (k := k) hp hn hnp
  have hdiv := Nat.mod_add_div ((extraIndex p n k + 1) * n) p
  rw [hquot] at hdiv
  change phase p n (extraIndex p n k) + p * (k + 1) = _ at hdiv
  dsimp [extra]
  nlinarith [hb.1]

theorem extraRank_extraIndex {p n k : Nat} (hp : 0 < p) (hn : 0 < n)
    (hnp : n < p) : extraRank p n (extraIndex p n k) = k := by
  unfold extraRank
  rw [extraIndex_quotient hp hn hnp]
  omega

theorem extraRank_bounds {p n i : Nat} (hp : 0 < p) (hn : 0 < n)
    (hi : i < p) (hextra : extra p n i) :
    0 < (i + 1) * n / p ∧ extraRank p n i < n ∧
      i * n < (extraRank p n i + 1) * p ∧
      (extraRank p n i + 1) * p ≤ (i + 1) * n := by
  have hdiv := Nat.mod_add_div ((i + 1) * n) p
  change phase p n i + p * ((i + 1) * n / p) = _ at hdiv
  have he : phase p n i < n := hextra
  have hpositive : 0 < (i + 1) * n / p := by nlinarith
  have hle : (i + 1) * n ≤ p * n := Nat.mul_le_mul_right n (by omega)
  have hquot : (i + 1) * n / p ≤ n := by nlinarith
  have hrank : extraRank p n i + 1 = (i + 1) * n / p := by
    dsimp [extraRank]
    omega
  refine ⟨hpositive, ?_, ?_, ?_⟩
  · dsimp [extraRank]
    omega
  · rw [hrank]
    nlinarith
  · rw [hrank]
    nlinarith

theorem extraIndex_extraRank {p n i : Nat} (hp : 0 < p) (hn : 0 < n)
    (hi : i < p) (hextra : extra p n i) :
    extraIndex p n (extraRank p n i) = i := by
  have hb := extraRank_bounds hp hn hi hextra
  have hpos : 0 < (extraRank p n i + 1) * p := Nat.mul_pos (by omega) hp
  unfold extraIndex
  apply Nat.div_eq_of_lt_le <;> omega

abbrev Key (p n : Nat) := (Fin p ⊕ Fin p) ⊕ Fin n

def extraVertex {p n : Nat} (hp : 0 < p) (hn : 0 < n) (k : Fin n) : Fin p :=
  ⟨extraIndex p n k.val, extraIndex_lt hp hn k.isLt⟩

theorem extraVertex_injective {p n : Nat} (hp : 0 < p) (hn : 0 < n)
    (hnp : n < p) : Function.Injective (extraVertex hp hn) := by
  intro left right hequal
  have h := congrArg (fun i : Fin p => extraRank p n i.val) hequal
  simp only [extraVertex, extraRank_extraIndex hp hn hnp] at h
  exact Fin.ext h

def endpoint {p n : Nat} (hp : 0 < p) (hn : 0 < n) : Key p n → Bool → Fin p
  | .inl (.inl i), _ => i
  | .inl (.inr i), false => i
  | .inl (.inr i), true => finRotate p i
  | .inr k, _ => extraVertex hp hn k

def threshold {p n : Nat} : Key p n → Nat
  | .inl (.inl i) => identityThreshold p n i.val
  | .inl (.inr i) => shiftedThreshold p n i.val
  | .inr k => extraThreshold p n (extraIndex p n k.val)

theorem threshold_le {p n : Nat} (hp : 0 < p) (hnp : n < p)
    (key : Key p n) : threshold key ≤ 4 * p := by
  rcases key with (i | i) | k
  · exact identityThreshold_le hp hnp
  · exact shiftedThreshold_le hp
  · exact extraThreshold_le hnp

def sample {p n : Nat} (hp : 0 < p) (hn : 0 < n)
    (key : Key p n) (coin : Fin (4 * p)) : Fin p × Bool :=
  let hint := decide (threshold key ≤ coin.val)
  (endpoint hp hn key hint, hint)

open scoped BigOperators

theorem sum_extraVertex {p n : Nat} (hp : 0 < p) (hn : 0 < n) (hnp : n < p)
    (i : Fin p) (weight : Fin p → Nat) :
    (∑ k : Fin n, if extraVertex hp hn k = i then weight (extraVertex hp hn k) else 0) =
      if extra p n i.val then weight i else 0 := by
  classical
  by_cases hi : extra p n i.val
  · let k : Fin n := ⟨extraRank p n i.val, (extraRank_bounds hp hn i.isLt hi).2.1⟩
    have hk : extraVertex hp hn k = i := by
      apply Fin.ext
      exact extraIndex_extraRank hp hn i.isLt hi
    rw [Finset.sum_eq_single k]
    · simp [hk, hi]
    · intro j _ hj
      have hne : extraVertex hp hn j ≠ i := by
        intro heq
        apply hj
        exact extraVertex_injective hp hn hnp (heq.trans hk.symm)
      simp [hne]
    · simp
  · have hne (k : Fin n) : extraVertex hp hn k ≠ i := by
      intro heq
      apply hi
      rw [← heq]
      exact extraIndex_extra hp hn hnp
    simp [hne, hi]

theorem before_rotate {p n : Nat} (hp : 0 < p) (i : Fin p) :
    before p n (finRotate p i).val = phase p n i.val := by
  letI : NeZero p := ⟨by omega⟩
  simp [before, phase, finRotate_apply, Fin.val_add, Nat.mul_mod, Nat.add_mod]

theorem phase_previous {p n : Nat} (hp : 0 < p) (i : Fin p) :
    phase p n ((finRotate p).symm i).val = before p n i.val := by
  have h := (before_rotate (n := n) hp ((finRotate p).symm i)).symm
  rw [Equiv.apply_symm_apply] at h
  exact h

/-- Exact count of the coin states entering any left endpoint. -/
theorem incoming_false {p n : Nat} (hp : 0 < p) (hn : 0 < n) (hnp : n < p)
    (i : Fin p) :
    (∑ key : Key p n, if endpoint hp hn key false = i then threshold key else 0) =
      2 * rangeSize p n := by
  classical
  simp only [Fintype.sum_sum_type]
  change ((∑ j : Fin p, if j = i then identityThreshold p n j.val else 0) +
    (∑ j : Fin p, if j = i then shiftedThreshold p n j.val else 0) +
    (∑ k : Fin n, if extraVertex hp hn k = i then
      extraThreshold p n (extraVertex hp hn k).val else 0)) = _
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have hx := sum_extraVertex hp hn hnp i (fun j => extraThreshold p n j.val)
  change _ + (∑ k : Fin n,
    if extraVertex hp hn k = i then extraThreshold p n (extraVertex hp hn k).val else 0) = _
  rw [hx]
  exact left_fiber_balance hp hnp

/-- Exact count of the coin states entering any right endpoint. -/
theorem incoming_true {p n : Nat} (hp : 0 < p) (hn : 0 < n) (hnp : n < p)
    (i : Fin p) :
    (∑ key : Key p n, if endpoint hp hn key true = i then 4 * p - threshold key else 0) =
      2 * rangeSize p n := by
  classical
  simp only [Fintype.sum_sum_type]
  change ((∑ j : Fin p, if j = i then 4 * p - identityThreshold p n j.val else 0) +
    (∑ j : Fin p, if finRotate p j = i then 4 * p - shiftedThreshold p n j.val else 0) +
    (∑ k : Fin n, if extraVertex hp hn k = i then
      4 * p - extraThreshold p n (extraVertex hp hn k).val else 0)) = _
  simp only [← (finRotate p).eq_symm_apply, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]
  have hx := sum_extraVertex hp hn hnp i (fun j => 4 * p - extraThreshold p n j.val)
  change _ + (∑ k : Fin n,
    if extraVertex hp hn k = i then 4 * p - extraThreshold p n (extraVertex hp hn k).val else 0) = _
  rw [hx]
  simp only [shiftedThreshold, phase_previous hp]
  exact right_fiber_balance hp hnp

def belowEquiv {length cut : Nat} (hle : cut ≤ length) :
    {coin : Fin length // coin.val < cut} ≃ Fin cut where
  toFun coin := ⟨coin.val.val, coin.property⟩
  invFun value := ⟨⟨value.val, by omega⟩, value.isLt⟩
  left_inv value := by cases value; rfl
  right_inv value := by rfl

def aboveEquiv {length cut : Nat} (hle : cut ≤ length) :
    {coin : Fin length // cut ≤ coin.val} ≃ Fin (length - cut) where
  toFun coin := ⟨coin.val.val - cut, by have := coin.val.isLt; have := coin.property; omega⟩
  invFun value := ⟨⟨value.val + cut, by have := value.isLt; omega⟩, by change cut ≤ value.val + cut; omega⟩
  left_inv value := by
    apply Subtype.ext
    apply Fin.ext
    dsimp
    have := value.property
    omega
  right_inv value := by
    apply Fin.ext
    dsimp
    omega

theorem sample_eq_iff {p n : Nat} (hp : 0 < p) (hn : 0 < n)
    (key : Key p n) (coin : Fin (4 * p)) (i : Fin p) (hint : Bool) :
    sample hp hn key coin = (i, hint) ↔ endpoint hp hn key hint = i ∧
      (if hint then threshold key ≤ coin.val else coin.val < threshold key) := by
  cases hint <;> by_cases h : threshold key ≤ coin.val
  all_goals simp [sample, h]
  omega

theorem coin_fiber_card {p n : Nat} (hp : 0 < p) (hn : 0 < n) (hnp : n < p)
    (key : Key p n) (i : Fin p) (hint : Bool) :
    Fintype.card {coin : Fin (4 * p) // sample hp hn key coin = (i, hint)} =
      if endpoint hp hn key hint = i then
        (if hint then 4 * p - threshold key else threshold key) else 0 := by
  classical
  by_cases he : endpoint hp hn key hint = i
  · simp only [he, ↓reduceIte]
    cases hint
    · have eqv : {coin : Fin (4 * p) // sample hp hn key coin = (i, false)} ≃
          {coin : Fin (4 * p) // coin.val < threshold key} :=
        Equiv.subtypeEquivRight fun coin => by simp only [sample_eq_iff, he, true_and, Bool.false_eq_true, ↓reduceIte]
      simpa using Fintype.card_congr (eqv.trans (belowEquiv (threshold_le hp hnp key)))
    · have eqv : {coin : Fin (4 * p) // sample hp hn key coin = (i, true)} ≃
          {coin : Fin (4 * p) // threshold key ≤ coin.val} :=
        Equiv.subtypeEquivRight fun coin => by simp only [sample_eq_iff, he, true_and, ↓reduceIte]
      simpa using Fintype.card_congr (eqv.trans (aboveEquiv (threshold_le hp hnp key)))
  · simp only [he, ↓reduceIte]
    apply Fintype.card_eq_zero_iff.mpr
    refine ⟨fun value => ?_⟩
    exact he ((sample_eq_iff hp hn key value.val i hint).mp value.property).1

/-- Every output and public hint has exactly the same finite fiber size.
This is exact counting, with no statistical approximation or PRG assumption. -/
theorem sample_fiber_card {p n : Nat} (hp : 0 < p) (hn : 0 < n) (hnp : n < p)
    (i : Fin p) (hint : Bool) :
    Fintype.card {state : Key p n × Fin (4 * p) //
      sample hp hn state.1 state.2 = (i, hint)} = 2 * rangeSize p n := by
  classical
  rw [Fintype.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun key coin => sample hp hn key coin = (i, hint)))]
  rw [Fintype.card_sigma]
  simp_rw [coin_fiber_card hp hn hnp]
  cases hint
  · exact incoming_false hp hn hnp i
  · exact incoming_true hp hn hnp i

/-- The binary pad is split into the two ordinary edge blocks and the
additional edge block without changing its uniform distribution. -/
def keyEquiv (p n : Nat) : Key p n ≃ Fin (rangeSize p n) :=
  ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin n))).trans finSumFinEquiv).trans
    (finCongr (by unfold rangeSize; omega))

/-- Equal-size sampler fibers give coordinates consisting of the field mask,
the public hint, and an auxiliary uniform coordinate.  This equivalence is
used only in proofs; executable sampling uses the explicit edge formulas. -/
noncomputable def coordinates {p n : Nat} (hp : 0 < p) (hn : 0 < n) (hnp : n < p) :
    Key p n × Fin (4 * p) ≃ (Fin p × Bool) × Fin (2 * rangeSize p n) :=
  (Equiv.sigmaFiberEquiv (fun state : Key p n × Fin (4 * p) =>
    sample hp hn state.1 state.2)).symm.trans
    ((Equiv.sigmaCongrRight fun output : Fin p × Bool =>
      Fintype.equivFinOfCardEq (sample_fiber_card hp hn hnp output.1 output.2)).trans
      (Equiv.sigmaEquivProd _ _))

theorem coordinates_fst {p n : Nat} (hp : 0 < p) (hn : 0 < n) (hnp : n < p)
    (state : Key p n × Fin (4 * p)) :
    (coordinates hp hn hnp state).1 = sample hp hn state.1 state.2 := by
  rfl

theorem sample_coordinates_symm {p n : Nat} (hp : 0 < p) (hn : 0 < n) (hnp : n < p)
    (value : (Fin p × Bool) × Fin (2 * rangeSize p n)) :
    let state := (coordinates hp hn hnp).symm value
    sample hp hn state.1 state.2 = value.1 := by
  dsimp only
  rw [← coordinates_fst hp hn hnp, Equiv.apply_symm_apply]

/-- A permutation of field masks lifts to a permutation of the hidden pad
and coin while preserving the public hint exactly.  Affine-table privacy will
instantiate this with addition by the selected coefficient difference. -/
noncomputable def transport {p n : Nat} (hp : 0 < p) (hn : 0 < n) (hnp : n < p)
    (permutation : Equiv.Perm (Fin p)) : Equiv.Perm (Key p n × Fin (4 * p)) :=
  (coordinates hp hn hnp).trans
    ((Equiv.prodCongr (Equiv.prodCongr permutation (Equiv.refl Bool)) (Equiv.refl _)).trans
      (coordinates hp hn hnp).symm)

theorem sample_transport {p n : Nat} (hp : 0 < p) (hn : 0 < n) (hnp : n < p)
    (permutation : Equiv.Perm (Fin p)) (state : Key p n × Fin (4 * p)) :
    let target := transport hp hn hnp permutation state
    sample hp hn target.1 target.2 =
      (permutation (sample hp hn state.1 state.2).1,
        (sample hp hn state.1 state.2).2) := by
  unfold transport
  change sample hp hn ((coordinates hp hn hnp).symm _).1
    ((coordinates hp hn hnp).symm _).2 = _
  rw [sample_coordinates_symm]
  rfl

def modulus : Nat := GarblingPrize.Protected.baseFieldModulus
def binaryRange : Nat := 2 ^ 255
def remainder : Nat := binaryRange - 2 * modulus

theorem concrete_range : 2 * modulus < binaryRange ∧ binaryRange < 3 * modulus := by
  norm_num [modulus, binaryRange, GarblingPrize.Protected.baseFieldModulus]

theorem concrete_remainder : 0 < remainder ∧ remainder < modulus := by
  have := concrete_range
  dsimp [remainder]
  omega

def tableBytes : Nat := (254 + 1) * 32
def candidateBytes : Nat := 91 * 11 * tableBytes

theorem tableBytes_eq : tableBytes = 8160 := by decide
theorem candidateBytes_eq : candidateBytes = 8168160 := by decide
theorem candidateBytes_below_goal : candidateBytes < 8200000 := by decide

end GarblingPrize.Submission.BinaryFieldHint
