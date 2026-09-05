# BLAKE3 label-to-label garbling challenge

Minimize the complete serialized garbling artifact for standard, unkeyed
BLAKE3 hashing of **exactly 64 input bytes to 32 output bytes**.

Each of the 512 input bits and 256 output bits has two independently supplied,
distinct **32-byte labels**. Bits are byte-major, least-significant-bit first.
The production-shaped interface is:

```text
garble(randomness, inputLabelPairs, outputLabelPairs) -> artifact
evaluate(artifact, 512 activeInputLabels) -> 256 activeOutputLabels
```

The garbler receives no message. The evaluator receives no plaintext message,
label pairs, secret seeds, or output decoder. It returns exactly the supplied
output label for each BLAKE3 digest bit, allowing composition with later
label-based computations. An honest artifact works for every 64-byte message
with its corresponding active labels. The security profile is **one-shot**:
functional reuse in tests does not authorize giving one adversary labels for
multiple messages under the same artifact.

## Reference and proof

The challenge imports, without copying or changing, zk.golf's generic GF(2)
BLAKE3 compression specification from
[`zksecurity/zk-golf-challenges` at `fb9e89a`](https://github.com/zksecurity/zk-golf-challenges/blob/fb9e89a5de99022a53089f0d11a18331c4c321a3/Challenge/Instances/Blake3CompressGF2Canonical/Spec.lean).
Its independent [natural-number specification](https://github.com/zksecurity/zk-golf-challenges/blob/fb9e89a5de99022a53089f0d11a18331c4c321a3/Challenge/Specs/Blake3.lean)
is also available as `referenceBytes`.

The specialization uses the standard IV as chaining value, counter zero,
block length 64, and flags `CHUNK_START | CHUNK_END | ROOT = 11`. It takes the
first 256 compression output bits. This is the ordinary 32-byte hash of the
64-byte message, **not** a parent-node compression of two chaining values.
The immutable official BLAKE3 64-byte test vector cross-checks byte order,
message permutation, seven rounds, and finalization.

The initial ranked track is **circuit optimization under a protected garbler**.
A submission provides 256 symbolic Boolean expressions and proves:

```lean
Blake3Prize.Protected.ValidCandidate candidate claimedBytes
```

The certificate requires equality to the protected reference for **all 512-bit
inputs**, plus a universal bound on the protected artifact-size function.
The baseline correctness theorem is compositional: a map preserving zero,
one, XOR, and AND commutes with zk.golf's carry recurrence, word operations,
quarter rounds, rounds, and finalization. The accepted axiom closure is limited
to `propext`, `Classical.choice`, and `Quot.sound`.

The protected lowerer shares structurally equal expressions, propagates
constants, and emits an acyclic XOR/AND circuit with complemented wires.
Structural comparison resolves hash collisions. Expressions are data; they
are never elaborated or executed as Lean metaprograms. Submissions can change
addition circuits, Boolean identities, factoring, and sharing. A different
garbling backend requires a separately reviewed challenge version.

## Artifact accounting

The backend uses 256-bit free-XOR labels and
[two half-gates per AND](https://eprint.iacr.org/2014/756). Internal wire pairs
share a fresh odd global XOR difference. Externally supplied label pairs need
no such correlation and need not have different low bits.

| Artifact component | Bytes |
| --- | ---: |
| Public constant label | 32 |
| 512 input adapters: selector byte + two 32-byte ciphertexts | 33,280 |
| AND tables: two 32-byte ciphertexts per AND | `64 × AND-count` |
| 256 output adapters: two 32-byte ciphertexts each | 16,384 |
| **Complete scored artifact** | **`49,696 + 64 × AND-count`** |

The initial submission has **10,281 AND gates** and **57,344 XOR gates**. Its
measured artifact is **707,680 bytes** (about 0.708 MB):
`49,696 + 64 × 10,281 = 707,680`. Including the fixed active input/output label
channels, total transferred bytes are **732,256**. This is the starting score
for optimization, not a lower bound on possible garbling size.

Each input adapter publishes a bit position where its two external labels
differ; the selected label chooses exactly one encrypted internal label.
Output adapters translate internal labels back to the independently supplied
output pairs. XOR gates, complements, rotations, and the fixed public circuit
use no garbled-table bytes. There are no uncounted headers, per-instance keys,
translation data, or circuit files. The entire returned byte string is scored;
truncation and trailing bytes are rejected. Fixed-width framing has Lean-checked
encode/decode round trips in both directions.

The 16,384-byte active input-label channel and 8,192-byte active output-label
channel are fixed and excluded from the artifact score. The report also shows
`totalTransferredBytes = artifactBytes + 24,576` to make that distinction
visible. It does not count private label pairs retained by their owner or an
oblivious-transfer protocol, neither of which is part of this interface.

## Security and trust boundary

This is an honest, one-shot garbling profile with computational privacy, under
the random-oracle assumptions for the domain-separated SHA-256 half-gates
hashes and label adapters. External pairs must be generated independently and
freshly, independently of the garbler's randomness. An evaluator receives only
one active label per input wire. No information-theoretic privacy claim about
finite 32-byte keys is made.

Lean proves the reference-expression semantics, byte formula, and the
per-coordinate half-gates correctness identity for arbitrary hash outputs.
It does **not** prove the cryptographic security reduction, SHA-256 security,
the full native implementation, or the expression lowerer's semantic
preservation. Those last two are protected, tested components of this track's
trusted computing base, alongside Lean's compiler/runtime. The isolated
verifier checks all 512 single-bit messages, random and fixed messages, exact
output labels, and a separate evaluator process. These tests complement the
semantic theorem; they are not a security proof.

This profile does not provide malicious-garbler security, input-label
validation/authentication, side-channel resistance, or multi-artifact
composition. A malformed artifact of the correct length can produce arbitrary
labels. The baseline is research software, not a production protocol.

## Run it safely

Lean 4.28.0, Clean, Mathlib, and zk.golf are pinned independently of the G1
challenge's toolchain. With `elan`, Python 3, Git, and a C compiler available:

```bash
./blake3/setup.sh
./blake3/benchmark.sh
```

Setup compiles the trusted bridge and snapshots pinned dependency sources and
build artifacts. The verifier overlays only the submission into a fresh build,
checks its exact theorem type and axiom closure, exports public topology, then
samples fresh labels and messages and measures real garbling/evaluation.
Results are written to `blake3/.yukon/blake3-64-labeled-hash-score.json` and
published in the BLAKE3 GitHub Actions summary.

Every build uses a **4 GiB aggregate RSS cap** and 30-minute timeout. Every
native export/test uses a **1 GiB cap** and five-minute timeout. Work runs
sequentially with one Lean thread and reduced CPU priority. A missing resource
monitor fails closed. Do not bypass these wrappers on a development machine.

Contestant edits belong only in `Blake3Prize/Submission/*.lean` and `score.txt`.
The protected digest, dependencies, reference, runtime, and workflow belong to
the challenge author. The G1 submission and its PR remain separate.
