# BLAKE3 challenge boundary

This challenge is separate from GarblingPrize. Contestants edit only
Blake3Prize/Submission/*.lean and its score.txt. Challenge-authoring changes
require explicit user authorization; this PR is authorized to redesign the
protected contract and use VCVio on Lean 4.33.1.

The reference is Clean's MIT-licensed standard unkeyed 64-byte BLAKE3 hash.
Every bit has two independently supplied distinct 32-byte labels. Evaluation
gets the known plaintext message, 512 active labels, and the artifact. It must
return the 256 selected output labels and protect every opposite input and
output label. Hiding plaintext message/digest bits is not required.

Submissions own construction, evaluation, artifact type, serialization, and
proofs. Do not prescribe Yao, half-gates, circuits, expressions, a lowerer, or
any gate-based byte formula. The optional half-gates baseline is uncertified;
its 707,680-byte measurement is not a ranked score under the neutral contract.

The common secret-release rule is separate from proof profiles. Initially the
profile is ClassicalBoundedQueryROM, using VCVio and a shared ideal oracle.
Record its exact bound and assumptions. Never claim the SHA-256 instantiation
is proved secure by the ideal-oracle theorem. Never admit a candidate's own
security claim as an assumption or let it choose its adversary class.

Use setup.sh, benchmark.sh, and scripts/baseline.py. They enforce 8 GiB CI /
4 GiB local build and 1 GiB native aggregate RSS caps, timeouts, one Lean
thread, and nice 10. Never set GITHUB_ACTIONS=true for a local build.
Run one build/test at a time. Never use an uncapped compilation or benchmark.

No proof gaps, local axioms, native_decide, unsafe/partial definitions, FFI,
initialization, metaprogram execution, macros, compiler substitution attributes,
namespace overrides, include_str, wf_preprocess, filesystem access, or extra unpinned dependencies in
submissions. The exact certificate and allowed axiom closure are audited.

Submission acceptance must execute the immutable base revision's workflow and
verifier. Admit only flat regular submission blobs after comparing complete
base/head Git trees. A PR-controlled digest cannot authenticate PR-controlled
rules. Protected-code authoring uses a separate non-ranking preview; its rules
become trusted only after review and merge into the base.

Keep every commit title below 50 characters, use unsigned commits, explain the
mathematics in the body, and keep PR #3 open and ready for CI.

The shared SecretRelease contract is author-owned and intentionally one file.
Keep reusable construction/security reductions outside it. BLAKE3 now instantiates the shared accepted predicate; migration evidence
remains outside its import graph. Preserve each game's semantics; G1's ideal-pad theorem is not
a finite-key ROM certificate. The challenge fixes validity, disclosure, key
law, error bounds, and forbidden claims before submissions; only submissions'
schemes/proofs may vary. Build the shared native check through the same caps.
Private-parameter leakage must be explicitly declared; do not infer it from a
typed reference result behind a lossy disclosure. Post-release recovery does
not establish withholding: enable the separate pre-release target when needed.
Full-label recovery does not imply absence of partial leakage. Keep these
goals and the separate executable acceptance obligations explicit.
