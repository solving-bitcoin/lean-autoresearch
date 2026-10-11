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
- Rust reference suite: **6 reference + 5 review tests passed**, 0 failed. The separate full-size test was
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

- The complete all-source Lean build, generated executable tools and their
  actual codec/algorithm correspondence. Protected, Threshold and the shared
  packed-runtime equivalence theorem have passed hosted Lean; see PROOF_STATUS.
  The local installer returned proxy 403; the restriction was not bypassed.
- Universal correctness, the complete sampled sharing law and the joint ROM
  reduction. The universal 48,752,768-byte artifact bound and abstract Shamir
  reconstruction/transport theorems have been checked; see PROOF_STATUS for
  exact scope and commits. The shared certificate remains `none`; no score.
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

## Follow-up runtime optimization

Interleaving the 16 independent Horner accumulators in contiguous Rust arrays
preserves every scalar polynomial evaluation and the fixed byte layout. The
independent Python ciphertext vectors and a new scalar-versus-interleaved test
pass. Under the same local build/native settings, Prepare fell from 61.13 s to
24.20 s; the full test fell from 69.17 s to 31.96 s (319,254,528-byte peak RSS).
No timeout, field, randomness distribution, hash domain or artifact format was
changed. This optimizes the independent reference only; generated Lean timing
still needs measurement and is not established by this result.

The first hosted reference run at d2c4f9f passed but measured the original
Prepare at 69.66 s and the full test at 77.92 s. Hosted Lean installation and
cache-key generation succeeded. There was no exact cache hit, so this run
provides no evidence of warm-cache performance.

The optimized hosted reference run at a2dce49 passed: Prepare 26.12 s, full
test 34.51 s, peak 320,299,008 bytes. This remains a Rust-only measurement.

The reference job for `f605fb5` passed all six reference tests, five review
tests and the separately invoked full-size test: Prepare 26.10 s, full test
34.47 s, peak 320,294,912 bytes. These measurements do not certify the candidate.
The optional shared packed-coin path has a universal equivalence proof checked
by hosted Lean. The BLAKE3 preview at `50e6007` passed the 256 MiB native memory
regression and the negative test rejecting a packed implementation without
its equivalence proof. The relevant shared files are unchanged at `da8f424`.
Its axiom audit listed only propext, Classical.choice and Quot.sound. This
checks the shared runtime path, not the WOTS algorithm or WOTS bundle.
The SDK per-tool limit remains 60 seconds and native RSS remains 1 GiB.

At `d048390`, the hosted reference job measured Prepare at 28.95 s, the full
test at 38.09 s and peak RSS at 320,221,184 bytes. All reference/review checks
passed. Hosted Lean checked Nonvacuity and the canonical Horner-result bridge;
BitMapping/InverseBridge errors still prevented a complete source build.

Both BLAKE3 and G1 authoring previews at `50e6007` completed successfully,
including native generated-tool tests and packed-coin tests. The corresponding
shared runtime, native regression and verifier sources remain unchanged at
`d048390`. This is compatibility evidence for those shared changes, not a
passing WOTS preview or a passing complete matrix for the current head.

When ordinary proof elaboration fails, the authoring checker now attempts a
separate runtime diagnostic importing the same `Sharing.construction` through
the protected public-key wrapper and generated four-tool CLI. It uses the
existing Rust SDK, 60-second per-tool timeout and 1 GiB native guard. Its entry
has no certificate; its metadata remains `not-audited`, and it creates no
acceptance report or exported archive. Every proof failure is still fatal.
When all source proofs compile, the normal isolated verifier runs directly.
Run 32 built and packaged SRTools, then its supplied-bundle integration test
failed after 64.27 seconds with the combined SDK timeout/side-output message.
The independent byte-for-byte generated-artifact test was not reached.
The next SDK diagnostic identifies the exact tool and cause without changing
the timeout, output limit or RSS guard. No generated-tool success is claimed.

The next author-preview scheduler builds the source import graph in dependency
order using the existing conservative Lean lexer. A failed prerequisite blocks
its dependents instead of repeatedly recompiling the same failure. Every
blocked module remains in the fatal rejection list. Independent modules still
build, and successful runs attempt all modules before the isolated verifier.
`check_author_graph.py` passed local failure-injection cases for complete
success, an ordinary proof failure, transitive blocked dependents, independent
work, immediate RSS/timeout rejection, and an import cycle (20,365,312-byte
peak under the normal native guard). These tests do not report a Lean pass.

Run 32 at `3d1bcb3` passed the independent reference job: Prepare 19.23 s,
three Expand calls 1.89/1.82/1.83 s, full fixed-artifact test 26.51 s, peak
320,348,160 bytes. These are Rust reference measurements, not Lean timings.

## Run 33 and timeout diagnostics

Hosted run 33 at `e959f9e` rejected the WOTS author check at its unchanged
1,800-second limit. The timeout branch discarded buffered Lean/runtime output;
no new proof or native pass is claimed from that run. The independent reference
job passed: Prepare 22.09 seconds, three-message test 30.51 seconds, peak RSS
320,405,504 bytes. The BLAKE3 and G1 previews both passed.

The following local changes await hosted validation: narrower tactic imports,
explicit compile/runtime stages, and bounded diagnostic tails on timeout.
The timeout remains fatal even if the child reports exit zero; the new
failure-injection regression confirms that behavior and truncation. The complete
resource/dependency regression suite passed under the temporary reaping
supervisor, peak RSS 107,085,824 bytes. The author-graph regression also passed.
The additional generated-tool test reusing one artifact for three later
messages compiled locally (peak 285,143,040 bytes), but has not run.

## Run 34: exact runtime failure and source repairs

Run 34 (`38095330840`, commit `baf5657`) completed the WOTS job with failure.
The original generated tools built and packaged; the standard integration test
reported 6 passed, 1 failed, 2 ignored, in 64.84 seconds. The failure is now
identified: `garble` exceeded its 60-second SDK limit at 60.005 seconds, with
no excessive side output and zero stdout/stderr bytes. The independent full
artifact correspondence/reuse test was not reached. Limits were not raised.

Lean checked `OracleSupport` and `MachineFieldReduction`. Two direct errors
blocked the remaining graph: the narrowed imports omitted the field instance
for `ZMod 65537`, and `FiniteOracleLaw` used an unqualified
`measurable_restrict`. The follow-up repairs those imports/names and removes
`MachineHorner`'s unnecessary dependency on interpolation. Its correspondence
proof remains unchecked; the submitted entry still uses the original scheme.

The follow-up diagnostic scheduler may select machine/cached implementations
only after their full equality module successfully compiles. Failure-injection
tests check successful selection, fallback after cached-proof failure, and
fallback to the original after the machine-proof prerequisite fails. Every
source failure still rejects the run. These local tests passed under the
native guard at 20,258,816-byte peak RSS; they do not establish a Lean pass.

The independent Rust reference job passed: Prepare 18.07 seconds, full
fixed-artifact three-message test 23.83 seconds, peak RSS 320,389,120 bytes.
Both the BLAKE3 and G1 previews passed. The next batch changes WOTS-only files.


## Run 35: checked machine equivalence, build timeout

Run 35 (`38097429288`, commit `d1648af`) selected the machine diagnostic after
source compilation. The tested gate only selects it after `MachineSharing`
compiles, so its UInt32 Horner, residue-only decoder and whole-construction
correspondence proofs passed. `LabelGuessing` and `OracleMeasureBridge` also
appear explicitly as compiled in the retained log. The latter includes the
finite-oracle law. Cached-chain equality did not pass.

The author process hit the unchanged 1,800-second limit while its diagnostic
native build was active. No machine performance or full-artifact comparison
result was produced. The 8 KB timeout tail omitted earlier direct errors;
blocked-module names alone are not sufficient to diagnose those proofs.
BLAKE3, G1 and the independent reference job passed. Rust Prepare took 30.94
seconds; the full three-message reference test took 39.32 seconds, with
320,262,144-byte peak RSS. These are not Lean measurements.

The next preview saves bounded per-module diagnostics incrementally and emits
them even after timeout. Local injected failures verify fatal rejection,
stale-log removal, continued independent checks and proof-gated optimization
selection (peak RSS 21,213,184 bytes). By default it returns source failures
without the optional runtime probe; successful sources still require the full
isolated verifier and native suite. The optional probe now explicitly checks
the equality module before building executable-only imports. This refactor,
plus the new fresh-cell and programming-fiber proof drafts, awaits Lean.
