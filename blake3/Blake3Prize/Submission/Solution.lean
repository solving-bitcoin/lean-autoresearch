import Blake3Prize.Protected.Target

namespace Blake3Prize.Submission
open Protected

/-- The optional half-gates baseline has no end-to-end secrecy/transport proof.
Use `some ⟨scheme, maxBytes, .classicalBoundedQueryROM, proof⟩` to enter a certified scheme.
No baseline size is presented as an accepted score before that proof exists. -/
def entry : Option CertifiedScheme := none

end Blake3Prize.Submission
