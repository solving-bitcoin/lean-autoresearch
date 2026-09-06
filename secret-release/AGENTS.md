# Shared challenge contract

This is author-owned code shared by challenges. Keep SecretRelease.lean thin,
construction-independent, and free of reusable construction/security reductions.
Lamport, HORS, OnesOnly, Preimage and ClassicalBoundedQueryROM stay in the core.
SecretRelease.Simulation is an optional import facade for pinned VCVio APIs;
imports alone do not establish simulator efficiency or real/ideal security.
Do not weaken an acceptance predicate or claim the G1 ideal-pad theorem is a
finite-key ROM certificate. New profiles must fix reviewed games and cost models.

Run builds/tests sequentially through blake3/scripts/resources.py guarded:
8 GiB CI / 4 GiB local aggregate build RSS, 1 GiB native RSS, one Lean
thread, and nice 10. Never set GITHUB_ACTIONS=true for a local build.
Never run an uncapped Lake/Lean/native build. BLAKE3's protected digest and
immutable-base overlay cover this package; preserve that boundary when moving it.
Every commit must describe the mathematics, be unsigned, and use a title below
50 characters. Keep PR #3 open for CI.

The shared runtime derives canonical byte/key codecs and generates all four
entrypoints. Uncertified candidates may run; only a complete Certificate indexed
by the exact scheme and bound can rank. Rust references and test success never
replace Lean proofs. Keep artifact serialization submission-owned and custom
hash-dependent/variable-size disclosures supported. Run Rust tests through
scripts/test_rust.py, which separates build and native aggregate caps.
