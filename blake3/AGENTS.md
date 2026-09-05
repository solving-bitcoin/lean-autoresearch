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

Use setup.sh, benchmark.sh, and scripts/baseline.py. They enforce 4 GiB build
and 1 GiB native aggregate RSS caps, timeouts, one Lean thread, and nice 10.
Run one build/test at a time. Never use an uncapped compilation or benchmark.

No proof gaps, local axioms, native_decide, unsafe/partial definitions, FFI,
initialization, metaprogram execution, macros, compiler substitution attributes,
namespace overrides, filesystem access, or extra unpinned dependencies in
submissions. The exact certificate and allowed axiom closure are audited.

Keep every commit title below 50 characters, use unsigned commits, explain the
mathematics in the body, and keep PR #3 open and ready for CI.
