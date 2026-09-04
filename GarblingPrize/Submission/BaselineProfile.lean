import GarblingPrize.Submission.FamilyArtifact

namespace GarblingPrize.Submission.BaselineProfile

/-!
# Size profile of the official construction

These declarations are diagnostics for the balanced-ternary/RCB/eleven-table
submission, not requirements of the protected challenge contract.
-/

def scalarDigits : Nat := 161
def projectiveMaps : Nat := scalarDigits
def bytesPerProjectiveMap : Nat := ProjectiveMap.mapByteCount
def totalArtifactBytes : Nat := FamilyArtifact.byteCount projectiveMaps

theorem scalarDigits_eq : scalarDigits = 161 := by decide
theorem bytesPerProjectiveMap_eq : bytesPerProjectiveMap = 177419 := by decide
theorem totalArtifactBytes_eq : totalArtifactBytes = 28564459 := by decide

end GarblingPrize.Submission.BaselineProfile
