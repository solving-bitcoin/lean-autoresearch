import WotsLamport.Submission.InverseBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Nodup

namespace WotsLamport.Submission

def fieldFactors (shares : List (Nat × List Nat)) (a : Nat)
    (initial : ZMod 65537 × ZMod 65537) : ZMod 65537 × ZMod 65537 :=
  shares.foldl (fun nd b => if a = b.1 then nd else
    (nd.1 * (-(b.1 : ZMod 65537)), nd.2 * ((a : ZMod 65537) - (b.1 : ZMod 65537)))) initial

theorem fieldFactors_products (shares : List (Nat × List Nat)) (a : Nat)
    (initial : ZMod 65537 × ZMod 65537) :
    fieldFactors shares a initial =
      (initial.1 * ((shares.filter fun b => decide (a ≠ b.1)).map
        fun b => -(b.1 : ZMod 65537)).prod,
       initial.2 * ((shares.filter fun b => decide (a ≠ b.1)).map
        fun b => (a : ZMod 65537) - (b.1 : ZMod 65537)).prod) := by
  induction shares generalizing initial with
  | nil => simp [fieldFactors]
  | cons b rest ih =>
    change fieldFactors rest a (if a = b.1 then initial else
      (initial.1 * (-(b.1 : ZMod 65537)),
       initial.2 * ((a : ZMod 65537) - (b.1 : ZMod 65537)))) = _
    rw [ih]
    by_cases h : a = b.1 <;> simp [h, List.filter_cons, mul_assoc]

/-- Interpret both accumulators of the actual interpolation loop in the field. -/
theorem interpolationFactors_field (shares : List (Nat × List Nat)) (a : Nat)
    (bounded : ∀ b ∈ shares, b.1 ≤ prime) (initial : Nat × Nat) :
    (((interpolationFactors shares a initial).1 : ZMod 65537),
      ((interpolationFactors shares a initial).2 : ZMod 65537)) =
      fieldFactors shares a (initial.1, initial.2) := by
  induction shares generalizing initial with
  | nil => rfl
  | cons b rest ih =>
    have hb := bounded b (by simp)
    have hr : ∀ x ∈ rest, x.1 ≤ prime := fun x hx => bounded x (by simp [hx])
    simp only [interpolationFactors, fieldFactors, List.foldl_cons] at *
    rw [ih hr]
    by_cases h : a = b.1
    · simp [h]
    · simp [h, fmul_field, fsub_field _ _ hb]

theorem field_coordinate_ne (a b : Nat) (ha : a < prime) (hb : b < prime)
    (hne : a ≠ b) : (a : ZMod 65537) ≠ (b : ZMod 65537) := by
  intro h
  have ha' : a < 65537 := ha
  have hb' : b < 65537 := hb
  have hm := (ZMod.natCast_eq_natCast_iff' a b 65537).mp h
  rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hm
  exact hne hm

theorem fieldFactors_denominator_nonzero (shares : List (Nat × List Nat))
    (a : Nat) (ha : a < prime) (bounded : ∀ b ∈ shares, b.1 < prime)
    (initial : ZMod 65537 × ZMod 65537) (hi : initial.2 ≠ 0) :
    (fieldFactors shares a initial).2 ≠ 0 := by
  induction shares generalizing initial with
  | nil => exact hi
  | cons b rest ih =>
    have hb := bounded b (by simp)
    have hr : ∀ x ∈ rest, x.1 < prime := fun x hx => bounded x (by simp [hx])
    simp only [fieldFactors, List.foldl_cons]
    by_cases h : a = b.1
    · simp only [if_pos h]
      exact ih hr initial hi
    · simp only [if_neg h]
      exact ih hr _ (mul_ne_zero hi (sub_ne_zero.mpr (field_coordinate_ne a b.1 ha hb h)))

theorem inverse_field (a : Nat) (ha : (a : ZMod 65537) ≠ 0) :
    (inverse a : ZMod 65537) = (a : ZMod 65537)⁻¹ := by
  calc
    _ = (inverse a : ZMod 65537) * ((a : ZMod 65537) * (a : ZMod 65537)⁻¹) := by
      rw [mul_inv_cancel₀ ha, mul_one]
    _ = ((inverse a : ZMod 65537) * (a : ZMod 65537)) * (a : ZMod 65537)⁻¹ := by ring
    _ = _ := by rw [inverse_mul_field a ha, one_mul]

/-- The concrete modular weight equals the Lagrange numerator divided by
its denominator. Bounds follow from the actual coordinate layout. -/
theorem interpolationWeight_field (shares : List (Nat × List Nat)) (a : Nat)
    (ha : a < prime) (bounded : ∀ b ∈ shares, b.1 < prime) :
    (interpolationWeight shares a : ZMod 65537) =
      (fieldFactors shares a (1,1)).1 / (fieldFactors shares a (1,1)).2 := by
  have hf := interpolationFactors_field shares a (fun b hb => (bounded b hb).le) (1,1)
  have h1 := congrArg Prod.fst hf
  have h2 := congrArg Prod.snd hf
  change ((interpolationFactors shares a (1,1)).1 : ZMod 65537) =
    (fieldFactors shares a (1,1)).1 at h1
  change ((interpolationFactors shares a (1,1)).2 : ZMod 65537) =
    (fieldFactors shares a (1,1)).2 at h2
  have hn : ((interpolationFactors shares a (1,1)).2 : ZMod 65537) ≠ 0 := by
    rw [h2]
    exact fieldFactors_denominator_nonzero shares a ha bounded (1,1) (by simp)
  simp only [interpolationWeight, fmul_field, inverse_field _ hn, div_eq_mul_inv]
  rw [h1, h2]

theorem lagrange_basis_zero {I : Type} [DecidableEq I] (s : Finset I)
    (v : I → ZMod 65537) (a : I) :
    (Lagrange.basis s v a).eval 0 =
      (∏ b ∈ s.erase a, -v b) / (∏ b ∈ s.erase a, (v a - v b)) := by
  simp only [Lagrange.basis, Polynomial.eval_prod, Lagrange.basisDivisor,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, zero_sub]
  rw [Finset.prod_mul_distrib]
  simp [div_eq_mul_inv, mul_comm]

/-- The concrete weight is exactly a Lagrange basis evaluation on the concrete
share rows. Distinctness is required of coordinates, not merely of whole rows. -/
theorem interpolationWeight_basis (shares : List (Nat × List Nat))
    (distinct : (shares.map Prod.fst).Nodup)
    (bounded : ∀ b ∈ shares, b.1 < prime) (a : Nat × List Nat) (ha : a ∈ shares) :
    (interpolationWeight shares a.1 : ZMod 65537) =
      (Lagrange.basis shares.toFinset (fun b => (b.1 : ZMod 65537)) a).eval 0 := by
  have hn : shares.Nodup := List.Nodup.of_map Prod.fst distinct
  have hf : (shares.filter fun b => decide (a.1 ≠ b.1)).Nodup := hn.filter _
  have hs : (shares.filter fun b => decide (a.1 ≠ b.1)).toFinset = shares.toFinset.erase a := by
    ext b
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq, Finset.mem_erase]
    constructor
    · rintro ⟨hb, hne⟩
      exact ⟨fun h => hne (congrArg Prod.fst h.symm), hb⟩
    · rintro ⟨hne, hb⟩
      exact ⟨hb, fun h => hne (List.inj_on_of_nodup_map distinct hb ha h.symm)⟩
  rw [interpolationWeight_field shares a.1 (bounded a ha) bounded,
    fieldFactors_products, lagrange_basis_zero]
  simp only [one_mul]
  rw [← List.prod_toFinset _ hf, ← List.prod_toFinset _ hf, hs]

theorem modular_sum_field (weighted : List (Nat × List Nat)) (limb initial : Nat) :
    ((weighted.foldl (fun (acc : Nat) a => fadd acc (fmul a.1 a.2[limb]!)) initial : Nat) : ZMod 65537) =
      (initial : ZMod 65537) +
        (weighted.map fun a => (a.1 : ZMod 65537) * ((a.2[limb]! : Nat) : ZMod 65537)).sum := by
  induction weighted generalizing initial with
  | nil => simp
  | cons a rest ih =>
    simp only [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    simp [fadd, fmul, prime, add_assoc]

/-- Every limb returned by the actual interpolation function is interpreted
by the corresponding Lagrange interpolation of those same share rows. -/
theorem interpolate_field (shares : List (Nat × List Nat))
    (distinct : (shares.map Prod.fst).Nodup)
    (bounded : ∀ b ∈ shares, b.1 < prime) :
    (interpolate shares).map (fun n : Nat => (n : ZMod 65537)) =
      (List.range 16).map (fun limb =>
        (Lagrange.interpolate shares.toFinset (fun b => (b.1 : ZMod 65537))
          (fun b => ((b.2[limb]! : Nat) : ZMod 65537))).eval 0) := by
  simp only [interpolate, List.map_map]
  apply List.map_congr_left
  intro limb _
  simp only [Function.comp_apply, modular_sum_field, Nat.cast_zero, zero_add,
    List.map_map]
  have hn : shares.Nodup := List.Nodup.of_map Prod.fst distinct
  rw [← List.sum_toFinset _ hn, Lagrange.interpolate_apply, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Function.comp_apply, Polynomial.eval_mul, Polynomial.eval_C]
  rw [interpolationWeight_basis shares distinct bounded a (List.mem_toFinset.mp ha)]
  ring

theorem share_coordinates_injective (shares : List (Nat × List Nat))
    (distinct : (shares.map Prod.fst).Nodup)
    (bounded : ∀ b ∈ shares, b.1 < prime) :
    Set.InjOn (fun b : Nat × List Nat => (b.1 : ZMod 65537)) shares.toFinset := by
  intro a ha b hb he
  have hma := List.mem_toFinset.mp ha
  have hmb := List.mem_toFinset.mp hb
  apply List.inj_on_of_nodup_map distinct hma hmb
  by_contra hne
  exact field_coordinate_ne a.1 b.1 (bounded a hma) (bounded b hmb) hne he

/-- Reconstruction for the actual limbwise interpolation loop. The premises
name the byte-decoding obligations which expansion must establish. -/
theorem interpolate_reconstruct (shares : List (Nat × List Nat))
    (distinct : (shares.map Prod.fst).Nodup)
    (bounded : ∀ b ∈ shares, b.1 < prime) (coefficients : Nat → List Nat)
    (degree_lt : ∀ limb < 16,
      (fieldPolynomial (coefficients limb)).degree < shares.length)
    (values : ∀ b ∈ shares, ∀ limb < 16,
      ((b.2[limb]! : Nat) : ZMod 65537) = (fieldPolynomial (coefficients limb)).eval (b.1 : ZMod 65537)) :
    (interpolate shares).map (fun n : Nat => (n : ZMod 65537)) =
      (List.range 16).map (fun limb => (evaluatePolynomial (coefficients limb) 0 : ZMod 65537)) := by
  rw [interpolate_field shares distinct bounded]
  apply List.map_congr_left
  intro limb hl
  have hlimb : limb < 16 := List.mem_range.mp hl
  have hn : shares.Nodup := List.Nodup.of_map Prod.fst distinct
  have hd : (fieldPolynomial (coefficients limb)).degree < shares.toFinset.card := by
    rw [List.toFinset_card_of_nodup hn]
    exact degree_lt limb hlimb
  have he := Lagrange.eq_interpolate_of_eval_eq
    (s := shares.toFinset) (v := fun b : Nat × List Nat => (b.1 : ZMod 65537))
    (r := fun b => ((b.2[limb]! : Nat) : ZMod 65537))
    (share_coordinates_injective shares distinct bounded) hd
    (fun b hb => (values b (List.mem_toFinset.mp hb) limb hlimb).symm)
  rw [← he]
  exact evaluatePolynomial_field (coefficients limb) 0

theorem modular_sum_lt (weighted : List (Nat × List Nat)) (limb initial : Nat)
    (hi : initial < prime) :
    weighted.foldl (fun acc a => fadd acc (fmul a.1 a.2[limb]!)) initial < prime := by
  induction weighted generalizing initial with
  | nil => exact hi
  | cons a rest ih =>
    rw [List.foldl_cons]
    exact ih _ (Nat.mod_lt _ (by decide))

theorem interpolate_lt (shares : List (Nat × List Nat)) :
    ∀ n ∈ interpolate shares, n < prime := by
  intro n hn
  unfold interpolate at hn
  obtain ⟨limb, _, rfl⟩ := List.mem_map.mp hn
  exact modular_sum_lt _ limb 0 (by decide)

theorem bounded_lists_eq (a b : List Nat)
    (ha : ∀ n ∈ a, n < prime) (hb : ∀ n ∈ b, n < prime)
    (he : a.map (fun n : Nat => (n : ZMod 65537)) = b.map (fun n : Nat => (n : ZMod 65537))) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simpa using he
  | cons x xs ih =>
    cases b with
    | nil => simp at he
    | cons y ys =>
      simp only [List.map_cons, List.cons.injEq] at he
      have hxy : x = y := by
        by_contra hne
        exact field_coordinate_ne x y (ha x (by simp)) (hb y (by simp)) hne he.1
      have htail : xs = ys := ih ys
        (fun n hn => ha n (by simp [hn])) (fun n hn => hb n (by simp [hn])) he.2
      rw [hxy, htail]

/-- Canonical field representatives upgrade reconstruction from congruence
to equality of the executable natural-number outputs. -/
theorem interpolate_reconstruct_nat (shares : List (Nat × List Nat))
    (distinct : (shares.map Prod.fst).Nodup)
    (bounded : ∀ b ∈ shares, b.1 < prime) (coefficients : Nat → List Nat)
    (degree_lt : ∀ limb < 16,
      (fieldPolynomial (coefficients limb)).degree < shares.length)
    (values : ∀ b ∈ shares, ∀ limb < 16,
      ((b.2[limb]! : Nat) : ZMod 65537) = (fieldPolynomial (coefficients limb)).eval (b.1 : ZMod 65537)) :
    interpolate shares = (List.range 16).map (fun limb => evaluatePolynomial (coefficients limb) 0) := by
  apply bounded_lists_eq _ _ (interpolate_lt shares)
  · intro n hn
    obtain ⟨limb, _, rfl⟩ := List.mem_map.mp hn
    exact evaluatePolynomial_lt _ _
  · simpa only [List.map_map, Function.comp_def] using
      interpolate_reconstruct shares distinct bounded coefficients degree_lt values

end WotsLamport.Submission
