import SecretRelease
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum

/-! Reviewed numerical presets; the challenge author chooses the profile. -/
namespace SecretRelease.Profiles

def rom128 : ClassicalBoundedQueryROM where
  maxQueries := 2^64
  error := fun q => (q + 1 : ℚ≥0) / 2^128
  nontrivial := by
    intro q hq
    have hq' : (q : ℚ≥0) ≤ (2^64 : ℚ≥0) := by exact_mod_cast hq
    calc
      (q + 1 : ℚ≥0) / 2^128 ≤ (2^64 + 1 : ℚ≥0) / 2^128 := by gcongr
      _ < 1 := by norm_num

end SecretRelease.Profiles
