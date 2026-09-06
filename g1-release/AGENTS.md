# Shared-contract G1 challenge

The user authorized this new challenge. The protected predicate is
SecretRelease.Certified G1Release.Protected.challenge, never the old ideal-pad
RankedClaim. Do not import a legacy score as a ROM certificate. Keep the
shared core thin; challenge-specific codec/math proofs belong here.

Private Q is any canonical BN254 point (including infinity), r is canonical
modulo the scalar modulus, and A is a valid finite-affine point. Inputs are
512 Lamport bits with uniform distinct 32-byte pairs; output is plaintext.
Fix reviewed validity, leakage and query/error bounds before submissions.
No gate language, garbling algorithm or modulus oracle is mandatory.

Contestants edit only G1Release/Submission/*.lean and score.txt. Preserve
immutable-base admission, source/axiom audits, exact serialized scoring, and
fresh compilation of local protected sources. No accepted score without the
complete shared certificate. SHA-256 through the trusted C backend remains a
heuristic instantiation of the ideal ROM.

Every build/test must use the sequential resource guards (8 GiB CI /
4 GiB local aggregate build RSS, 1 GiB native RSS, one Lean thread, nice 10).
Never set GITHUB_ACTIONS=true for a local build. Never run a naked Lake,
Lean or native benchmark. Commits must be unsigned, have titles below 50
characters, and explain the math. Keep PR #3 open for CI.
