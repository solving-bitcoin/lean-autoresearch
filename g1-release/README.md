# Q + [r]A — SecretRelease challenge

Minimize the **universal serialized artifact byte bound** for a private BN254
map `A ↦ Q + [r]A`. This is a separate challenge using the shared
[`SecretRelease.Certified`](../secret-release/SecretRelease.lean) contract.
The old G1 challenge and its accepted ideal-pad score remain separate.

The complete challenge-specific security declaration is
[`G1Release/Protected/Target.lean`](G1Release/Protected/Target.lean).
It imports the existing BN254 prime certificate, curve, group law, and canonical
point representation. No Yao circuit language, gate count, modulus oracle,
half-gates construction, or mandatory arithmetic strategy appears in acceptance.

| Item | Fixed contract |
| --- | --- |
| Private parameters | Canonical point `Q` (including infinity), scalar `0 ≤ r < Fr` |
| Known evaluator input | Canonical finite-affine point `A` on BN254 `y² = x³ + 3` |
| Input disclosure | 512 Lamport bits, one active 32-byte label per bit |
| Key distribution | Independent uniform distinct label pairs; independent of coins and oracle |
| Output | Canonical plaintext point `Q + [r]A`, including infinity |
| Post-release forbidden claim | Recover any opposite input label (one indexed full-label guess) |
| Private-map privacy | Indistinguishability of any two `(Q,r)` with the same output at the known `A` |
| Oracle | Shared ideal random function, arbitrary byte strings → 256-bit labels |
| Adversary | Classical, static known input, one release; arbitrary local computation |
| Reviewed bound | At most `q ≤ 2^64` oracle queries; error `(q+1)/2^128` |
| Correctness | Exact, for every hash function, private parameter, key assignment, coins, and valid input |
| Score | Kernel-proved maximum of the complete serialized artifact, in bytes |

The evaluator receives both the active input labels and the correct plaintext
result for free in the security experiment. Private leakage is **exactly** the
canonical result bytes; an injectivity proof connects this to equality of the
mathematical point. In particular, at a fixed input, `(Q,r)` has the same leakage
as `(Q+[r]A,0)`. The comparison is meaningful even with unlimited local
computation; publishing `r` would distinguish such pairs.

These are post-release recovery and equal-result privacy goals. They are not a
bounded-simulator theorem, an adaptive/multiple-release theorem, or a promise
that no partial information about labels leaks. Pre-release withholding is not
enabled. The result itself is allowed to leak whatever it mathematically
reveals. `SecretRelease.Simulation` remains available as an optional proof
infrastructure import; importing it does not prove simulation security.

## Submission

Edit only flat `G1Release/Submission/*.lean` files and `score.txt`:

```lean
import G1Release.Protected.Target
namespace G1Release.Submission
-- Supply a runnable scheme with an optional, exactly indexed certificate.
def entry : Option (SecretRelease.Candidate G1Release.Protected.challenge) := none
end G1Release.Submission
```

A certificate includes your scheme, canonical artifact encode/decode proofs,
exact correctness through serialization, the universal byte bound, opposite
input-label secrecy, and private-map privacy. Algorithms and artifact formats
belong to the submission. All required public instance data must be serialized
in the artifact, apart from the explicitly fixed input/output channels above.
Proofs may use the pinned libraries; executable methods must compile and run
within the protected limits. The certificate axiom closure permits only
`propext`, `Classical.choice`, and `Quot.sound`.

The checked-in entry is **unranked** (`none`, `score.txt = unranked`). No
construction has yet supplied the finite-label ROM certificate. In particular,
the old **5,940,480-byte** ideal-pad construction is not certified here. Its
arithmetic and transport theorems can guide a submission, but its security
proof does not establish the shared finite-key ROM game. The protected 32,868-byte
runner fixture deliberately publishes `(Q,r)`, all labels, and its coins and is only an I/O test; it has
no security certificate and is never ranked.

## Binary interface

Every integer uses 32-byte little-endian encoding. Within each byte, bit 0 is
the least significant bit; x precedes y in the 512 input bits.

- `A.bin`: 64 bytes, `x || y`, canonical coordinates on the curve. Infinity is
  excluded from the input type.
- `output.bin` / Q: 65 bytes, `tag || x || y`. Tag 1 is a valid finite-affine
  point. Infinity is **65 zero bytes**; nonzero padding and other tags reject.
- `private.bin`: 97 bytes, canonical Q encoding followed by canonical r.
- `pairs.bin`: 32,768 bytes, bit order 0…511, `label0 || label1` for each bit;
  equal labels within a pair reject.
- `active.bin`: 16,384 bytes, one label selected by each encoded input bit.
- `coins.bin`: exactly the number of randomness bytes declared by the scheme.

```sh
./g1-release/setup.sh
./g1-release/benchmark.sh --allow-unranked  # authoring only

g1-release/.yukon/bundle/challenge describe
g1-release/.yukon/bundle/encode A.bin pairs.bin known.bin active.bin
g1-release/.yukon/bundle/garble coins.bin private.bin pairs.bin empty.bin artifact.bin
g1-release/.yukon/bundle/evaluate artifact.bin known.bin active.bin output.bin
```

`empty.bin` is the empty key encoding for plaintext outputs. All four tools are
generated by the shared library; authors write no I/O entrypoints. The current
candidate is missing, so garble/evaluate report that state, while encode and
reference work. Implemented uncertified candidates can run without a proof;
their accepted score remains null. See the [shared protocol](../secret-release/ARCHITECTURE.md).

The verifier exports the exact audited bundle. Rust SDK tests use independent
Arkworks BN254 arithmetic and compare reference bytes and actual released
outputs. Shared trusted C SHA-256 is tested against Rust SHA-256 at padding
boundaries. **The ideal-oracle instantiation remains heuristic / unproved.**

## CI and trust

All local sources (this challenge, shared contract, and reused G1 mathematics)
are freshly compiled in an isolated tree. Only pinned and authenticated external
Git dependency caches are reused. Builds are sequential, one Lean thread,
nice 10, with an 8 GiB CI / 4 GiB local aggregate RSS cap; native checks use
1 GiB in both environments. Time, process,
output, file-size, and combined package disk limits are also enforced.

`secret-release-authoring-preview` tests rule changes and publishes the executable
and report, but **never accepts a score**. After these rules are reviewed and
merged, `secret-release-trusted-submission` executes the immutable base workflow and
verifier. It compares the complete base/head Git trees and admits only regular
submission blobs. Editing protected rules and recomputing `protected.sha256`
cannot pass that admission step. The digest is an internal consistency check,
not the trust anchor.
