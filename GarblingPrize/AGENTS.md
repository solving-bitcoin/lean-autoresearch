# Challenge work boundary

Only `GarblingPrize/Submission` is contestant-editable. Protected files define
the current `bn254-g1-hidden-affine-map` profile.

Submissions may replace every internal construction choice, but they must
export the exact protected ranked claim and may not move evaluator-visible
per-instance data into labels, keys, generated modules, executables, output
representatives, environment state, or auxiliary files.

Submissions may import the pinned `Mathlib.*` and `CompPoly.*` module trees
directly. They may not import local modules outside
`GarblingPrize.Protected.Target` and `GarblingPrize.Submission.*`, or add new
dependencies. Internal techniques are unrestricted by the G1-only theorem:
the official solution's balanced-ternary and RCB/Jacobian code is a baseline,
not part of the contract. Do not use `sorry`, `admit`, `axiom`, `unsafe`,
`partial`, `implemented_by`, `extern`, native `export` attributes, tracing,
kernel bypasses, environment mutation, or build-time code execution.

Every submission's `Scheme.garble` receives the protected typed
`InternalOracle`; candidates cannot define a separate seed-to-randomness
instantiation. The protected executable expands one 32-byte internal seed with
HMAC-SHA256 and exact rejection sampling for every positive modulus through
`2^3072`. Label pairs are supplied separately and are never derived by the
production Lean API. Purpose addresses are unbounded and there is no query
budget. The runner invokes the submitted `Scheme` methods directly, so a
separate fast executable implementation is not an accepted substitute. The
generic runner is elaborated inside the protected module tree before any
submission import; submissions must not declare names in
`GarblingPrize.Protected` or `GarblingPrize.Executable`.
