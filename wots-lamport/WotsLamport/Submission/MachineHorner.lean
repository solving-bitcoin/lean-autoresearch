import WotsLamport.Submission.MachineFieldReduction

namespace WotsLamport.Submission

/-- A proposed executable optimization. This module is not yet wired into the
candidate. The coordinate bound ensures that UInt32 arithmetic cannot wrap. -/
def machineHorner : List UInt32 → UInt32 → UInt32 → UInt32
  | [], _, initial => initial
  | a :: rest, x, initial => machineHorner rest x (reduceMachineField (a + x * initial))

theorem machineHorner_step (a x acc : UInt32)
    (ha : a.toNat < prime) (hx : x.toNat ≤ 1984) (hs : acc.toNat < prime) :
    ((a + x * acc) % 65537).toNat = (a.toNat + x.toNat * acc.toNat) % prime := by
  have hb : x.toNat * acc.toNat ≤ 1984*65536 :=
    Nat.mul_le_mul hx (by dsimp [prime] at hs; omega)
  have hm : x.toNat * acc.toNat < 2^32 := by omega
  have hadd : a.toNat + x.toNat * acc.toNat < 2^32 := by
    dsimp [prime] at ha
    omega
  simp only [UInt32.toNat_mod, UInt32.toNat_add, UInt32.toNat_mul]
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hadd]
  rfl

theorem machineHorner_fold (coefficients : List UInt32) (x initial : UInt32)
    (hc : ∀ a ∈ coefficients, a.toNat < prime)
    (hx : x.toNat ≤ 1984) (hi : initial.toNat < prime) :
    (machineHorner coefficients x initial).toNat =
      coefficients.foldl (fun acc a => (a.toNat + x.toNat * acc) % prime) initial.toNat := by
  induction coefficients generalizing initial with
  | nil => rfl
  | cons a rest ih =>
    have ha := hc a (by simp)
    have hs := machineHorner_step a x initial ha hx hi
    have hb : ((a + x * initial) % 65537).toNat < prime := by
      rw [hs]
      exact Nat.mod_lt _ (by decide)
    change (machineHorner rest x (reduceMachineField (a + x * initial))).toNat = _
    rw [reduceMachineField_eq_mod]
    rw [ih (initial := (a + x * initial) % 65537)
      (hc := fun b hb => hc b (by simp [hb])) (hi := hb), hs]
    rfl

theorem fusedHorner_step (a x acc : Nat) :
    (a + x*acc) % prime = fadd a (fmul x acc) := by
  simp [fadd, fmul, Nat.add_mod]

/-- Reversing once per polynomial allows all its evaluation points to share
the same coefficient list. This is a mathematical identity for every input. -/
theorem reversedHorner_eq (coefficients : List Nat) (x : Nat) :
    coefficients.reverse.foldl (fun acc a => (a+x*acc)%prime) 0 =
      evaluatePolynomial coefficients x := by
  simp only [List.foldl_reverse, fusedHorner_step, evaluatePolynomial]

def machineCoefficients (coefficients : List Nat) : List UInt32 :=
  coefficients.reverse.map fun a => UInt32.ofNat (a % prime)

def evaluateMachinePolynomial (coefficients : List UInt32) (x : Nat) : Nat :=
  (machineHorner coefficients (UInt32.ofNat x) 0).toNat

theorem machineCoefficient_toNat (a : Nat) :
    (UInt32.ofNat (a % prime)).toNat = a % prime := by
  apply UInt32.toNat_ofNat_of_lt'
  exact (Nat.mod_lt a (by decide : 0 < prime)).trans (by decide)

/-- Exact correspondence for arbitrary natural coefficients and every
coordinate the artifact uses. Preparation is shared across all those points. -/
theorem evaluateMachinePolynomial_eq (coefficients : List Nat) (x : Nat)
    (hx : x ≤ 1984) :
    evaluateMachinePolynomial (machineCoefficients coefficients) x =
      evaluatePolynomial coefficients x := by
  have hx32 : (UInt32.ofNat x).toNat = x :=
    UInt32.toNat_ofNat_of_lt' (by change x < 4294967296; omega)
  have hc : ∀ a ∈ machineCoefficients coefficients, a.toNat < prime := by
    intro a ha
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp ha
    rw [machineCoefficient_toNat]
    exact Nat.mod_lt _ (by decide)
  unfold evaluateMachinePolynomial
  rw [machineHorner_fold _ _ _ hc (by simpa only [hx32] using hx) (by decide)]
  simp only [machineCoefficients, List.foldl_map, machineCoefficient_toNat, hx32,
    List.foldl_reverse]
  change coefficients.foldr (fun a acc => (a % prime + x * acc) % prime) 0 = _
  have step : (fun a acc : Nat => (a % prime + x * acc) % prime) =
      (fun a acc => fadd a (fmul x acc)) := by
    funext a acc
    simp [fadd, fmul, Nat.add_mod]
  rw [step]
  rfl

end WotsLamport.Submission
