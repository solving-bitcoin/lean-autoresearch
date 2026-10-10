# Local validation — 2026-10-10

Base checkout: `solving-bitcoin/lean-autoresearch`, branch `work`, commit
`b344b78a80eac105161a75e3a02f0b0b18a8b47b`. This is the baseline for the feature branch and draft PR.
Rust toolchain: `rustc 1.97.1 (8bab26f4f 2026-07-14)`.

## Completed checks

- Python: all 961 checksum totals, 246,016 message-bit mappings, 10,752
  weighted telescoping cases, 1,920 adjacent antichain comparisons, field and
  serialized-layout arithmetic.
- Independent Python/Rust agreement: public-key/signature hashes, 67 encoded
  digits and 20 encrypted-share byte vectors, including checksum coordinates.
- Rust reference suite: **6 reference + 4 review tests passed**, 0 failed. The separate full-size test was
  initially ignored in this suite and then explicitly executed. The generated
  Lean integration test was filtered out locally because no Lean bundle exists;
  the shared benchmark does not filter it out.
- Full-size reference: **1 passed** in **69.17 seconds**, peak aggregate RSS
  **319,229,952 bytes**, under the normal 1 GiB/300-second native guard. One
  fixed **48,752,768-byte artifact** produced all 256 correct fixed labels for
  three later messages (all-zero, all-ff, and bytes 00..1f). This is a universal
  interface exercised on three samples, not a universal proof or safe key reuse.
- Full-closure tests directly enumerate all reachable nodes and all exposed
  shares, rather than relying on the official Expand selector guard.
- Two signatures (00 and ff) demonstrably recover all 67 seeds; the test then
  recovers both labels and signs a third message. This documents the one-time
  boundary instead of claiming multi-use security.
- Toy F_7 Shamir test enumerates all degree-2 coefficient pairs and verifies
  identical two-share distributions for every secret. It is not a proof for
  this candidate or the shared oracle.

Useful raw logs are under the ignored `wots-lamport/.yukon/` directory:
`rust-build.txt`, `rust-tests-reference.txt`, `full-reference.txt`.

## Not validated

- Lean parsing/elaboration/kernel proofs, generated executable tools and their
  actual codec/algorithm correspondence. The official installer host returned
  proxy 403; the restriction was not bypassed.
- Universal correctness and artifact-size theorems, Shamir privacy and the
  joint ROM reduction. The shared candidate certificate is `none`; no score.
- Equivalence for all accepted raw stacks and Bitcoin Core consensus/policy validity.
- Adaptive security, simulation/GC composition, malicious setup or a full
  binding/availability/fraud protocol.
- Lean performance within the unchanged SDK's 60-second per-tool timeout.
  The full Rust test's total runtime is not a measurement of a generated Lean
  tool and does not establish this tighter limit.

The original verifier regression suite also requires a reaping init/supervisor
in this container: PID 1 is `tail`, leaving killed descendants as zombies.
The unchanged suite passes under a temporary child-reaping supervisor; its
normal invocation still fails here. No source change hides that failure.

See [PROOF_STATUS.md](PROOF_STATUS.md) for the precise theorem backlog and
[README.md](README.md) for reproducible commands and the frozen model profile.

## Additional independent review

The full reference run measured Prepare at 61.13 seconds and each Expand at
1.90–2.09 seconds. The separate SDK per-tool limit is 60 seconds: generated
Lean performance remains a material risk, and Rust timing does not resolve it.
The review tests cover domain separation, malformed input, endpoint exclusion,
and a degenerate-coins security counterexample. Arithmetic checks cover all
65,536 nonzero field inverses and the exact coefficient-sampling bias; these
are finite checks, not the missing general Shamir/privacy proof.

Three tests in the unmodified upstream revision passed under the same resource
guards: `hash_profiles_match_independent_python_vectors` (0.02 s),
`sha256_chain_binds_all_digits_and_rejects_wrong_widths` (1.19 s), and
`both_hashes_roundtrip_all_profiles_and_message_boundaries` (9.98 s).
The largest runtime RSS was 51,556,352 bytes. The build used 1,205,002,240 bytes.
These execute the upstream strict raw-script interpreter with its configured
stack limit. They do not establish every raw-witness equivalence, Bitcoin Core
consensus validity or relay policy; deployment remains unclassified.
