import G1Release.Protected.Target

namespace G1Release.Submission

/-- Enter `some certificate` only after proving every shared-contract field.
The legacy 5,940,480-byte ideal-pad theorem is not a finite-key ROM certificate. -/
def entry : Option G1Release.Protected.CertifiedScheme := none

end G1Release.Submission
