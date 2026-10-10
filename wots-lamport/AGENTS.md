# WOTS-to-Lamport authoring boundary

This is an experimental, unranked authoring track. Read README.md and
PROOF_STATUS.md before changing claims. All Lean sources are unchecked until
the pinned compiler actually runs. No sorry, new axioms, native_decide, or
candidate-controlled security assumptions. A missing certificate never ranks.

The first track is 32-byte direct-base-16 WOTS, 67 correlated SHA-256 chains,
independent 32-byte starts, strict full-width exact-hash verifier semantics.
Do not replace it by a digest domain or independent per-digit credentials.
The weighted checksum has weights 1,8,64; its ordinary digit sum is NOT fixed.
Canonical signing, semantic raw-witness interpretation, Script execution,
malicious setup and adaptive/compositional security are separate statements.

Only flat WotsLamport/Submission/*.lean and score.txt are competitor editable.
Protected/ includes all games, public-key wrapping and numerical targets.
Keep the shared immutable-base admission and kernel/source/axiom audits.
Use scripts/check_local.py for available checks and setup.sh/benchmark.sh for
Lean validation. All builds/tests run sequentially through the shared guards:
4 GiB local build RSS, 1 GiB native RSS, one Lean thread, nice 10. Never set
GITHUB_ACTIONS=true locally. Do not bypass a network denial to obtain Lean.
