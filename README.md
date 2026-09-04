# Lean Autoresearch

> [!WARNING]
> This repository contains experimental research software. Interfaces, proofs,
> artifact formats, security assumptions, and implementation details may change
> without notice. The code may contain bugs and has not been independently
> audited. Do not use it in production or rely on it to protect funds, secrets,
> or other high-value assets. The Lean proofs cover only the explicitly stated
> mathematical model; they do not establish end-to-end security of the native
> executable or a larger protocol integration. See [SECURITY.md](SECURITY.md)
> for vulnerability reporting instructions.

This repository will include experiments with Lean and autoprove challenges
designed to measure how far formally specified constructions can be optimized
while preserving machine-checked correctness.

## Research directions

### 1. Optimize existing primitives

Search the space of known constructions for implementations that are smaller,
cheaper, faster, or otherwise better.

These problems have objective evaluation functions and parallelize well,
making them useful early targets for autonomous research.

Related optimization competitions include:

- [Proximity Prize](https://github.com/proximity-prize/proximity-prize), which
  defines Lean-checked optimization challenges for certified protocol bounds;
- [ZPrize](https://www.zprize.io/), focused on accelerating zero-knowledge
  cryptography;
- the [SAT Competition](https://satcompetition.github.io/), which compares SAT
  solvers on standardized benchmarks; and
- [SMT-COMP](https://smt-comp.github.io/), which evaluates SMT solvers across
  standardized tracks and theories.

This repository follows the challenge structure used by
[Proximity Prize](https://github.com/proximity-prize/proximity-prize), including
a protected target, an editable submission area, machine-checked score claims,
benchmark metadata, and an isolated verifier.

## Current challenge: BN254 G1 hidden affine map

Minimize the universally proved serialized artifact size for the ideal
garbling function

```text
(Q, r ; A) ↦ Q + [r]A.
```

`Q` and the canonical BN254 scalar `r` are hidden garbler inputs. `A` is a
valid canonical finite-affine BN254 G1 point known to the evaluator. The
evaluator receives the artifact plus exactly 512 genuine active label oracles
and returns one protected canonical G1 output, including one unique infinity.
Setting `Q = infinity` is an ordinary covered input and gives the BABE
operation `[r]A`.

## What a submission proves

The score is the smallest `maxBytes` for which Lean checks:

```lean
GarblingPrize.Protected.ValidCandidate scheme maxBytes
```

That theorem requires:

1. universal correctness for every protected `InternalOracle`, supplied
   `LabelPairs`, and valid affine input;
2. exact equality of complete public-view distributions whenever two hidden
   functions agree at the selected `A`;
3. exact two-way artifact codec laws; and
4. a universal bound on the actual `ByteArray.size` returned by
   `Scheme.garbleBytes`.

`PublicView` contains the exact artifact bytes, all 512 active label functions,
and the evaluator result. The ideal theorem gives identical source/target
public-view distributions and therefore equal probabilities for every
measurable event.

## Frozen boundary

Only `GarblingPrize/Submission` is contestant-editable. The protected target
fixes:

- BN254 G1 with `y² = x³ + 3`;
- finite canonical affine evaluator inputs;
- arbitrary `Q`, including infinity;
- canonical scalar `r`;
- 512 little-endian coordinate bits;
- a typed ideal internal oracle indexed by a positive modulus at most
  `2^3072` and an unbounded purpose;
- labels of type `Purpose → Bytes 32`;
- canonical outputs; and
- the exact scored byte channel.

Active labels are not scored. There are no artifact framing/version bytes: the
ranked artifact is one exact-length byte vector, and every byte is counted. The
decoder rejects truncation and trailing bytes. Submissions may redesign the
scalar representation, projective-map count, addition formula, polynomial
factorization, affine tables, sharing, and artifact encoding.

## Official baseline

The exported baseline is a computable balanced-ternary construction with 161
complete projective selector maps. Each map uses 11 affine tables and 254
significant-coordinate rows. Its exact artifact bound is:

```text
28,564,459 bytes.
```

The submission proves scalar decomposition, complete projective-map semantics
(including identity, doubling, and inverse cases), public ternary
recomposition, exact codec laws, the byte bound, and whole-artifact ideal
privacy. The earlier GLV experiment remains in the repository but is outside
the official import graph.

## Ideal proof and protected executable

The theorem has two independent ideal primitives:

- `InternalOracle := (m : SamplingModulus) → Purpose → Fin m.value`, where
  every `(modulus, purpose)` coordinate is exactly uniform; and
- `LabelPairs := BitIndex → Bool → Purpose → Bytes 32`, where every
  label-pad coordinate is exactly uniform.

Both use countable product measures, so distinct coordinates are independent
and `Purpose := Nat` remains unbounded. Lean proves exact
information-theoretic equality under `internalOracleLaw × labelPairsLaw`.
`Scheme.Randomness` and `Scheme.SeedInstantiation` are not part of the
protected contract. The official submission may use a private structured
randomness record, but it must derive that record inside its proved `garble`
from the protected oracle.

The executable owns the only seed-to-internal-oracle implementation. Given a
fresh 32-byte internal seed, it uses the fixed domain
`g1-q-plus-rA/internal-uniform/v1`, HMAC-SHA256, and between one and twelve
256-bit blocks according to the requested modulus. It rejects candidates at
or above `floor(2^B / m) * m` before reducing modulo `m`; there is no modulo
bias in the ideal-PRF model. The loop has no attempt cap or failure-probability
API. The native C/FFI implementation is an executable trust boundary: Lean
does not prove HMAC security or rejection-loop termination.

Production callers supply purpose-indexed `LabelPairs` independently. Lean
does not derive external labels. The production-shaped entry points are:

```text
garbleWithSeedAndLabelPairs(seed, Q, r, labelPairs) -> artifact
evaluateWithLabels(artifact, A, activeLabels) -> Q + [r]A
```

The garbler has no `A` argument, so one artifact can be evaluated at different
valid `A` values with the corresponding active labels.

The concrete privacy statement relies on two assumptions:

1. with a fresh uniformly random internal seed, the protected HMAC oracle is
   computationally indistinguishable from `internalOracleLaw` for the queries
   made by the executable; and
2. independently generated external label pads are computationally
   indistinguishable from `labelPairsLaw`.

Operationally, use a fresh internal seed for every artifact, and keep external
label keys fresh or correctly domain-separated and independent. Lean does not
prove these PRF assumptions, seed freshness, side-channel security,
multi-artifact composition, or the complete BABE transcript.

The CLI is only a test/benchmark harness. It derives labels from a separate
test-only seed. Production secrets should not be passed in argv; a later Rust
adapter will own external label derivation and the stable BABE ABI.

## Trust and axiom boundary

The generic runner is elaborated before `Submission.Solution` is imported. The
post-import executable bridge passes only `scheme` and `claimedBytes`, so a
submission cannot replace seed expansion or measured runner logic. The
isolated verifier checks SHA/HMAC and exact rejection vectors through the
12-block maximum and audits submission objects for collisions with all
protected native symbols.

The ranked theorem's exact axiom closure is:

```text
propext
Classical.choice
Quot.sound
```

The project is pinned to Lean 4.33.1, Mathlib 4.33.1, and CompPoly 4.33.1.
The verifier rejects local axioms, forbidden source constructs, additional
dependencies, and changes to pinned dependency sources or authenticated build
artifacts.

## Running the challenge

```bash
./setup.sh
lake exe g1-challenge selftest
lake exe g1-challenge sample 0000000000000000000000000000000000000000000000000000000000000000 17 0
lake exe g1-challenge run-case \
  --randomness-seed 0000000000000000000000000000000000000000000000000000000000000000 \
  --label-seed 1111111111111111111111111111111111111111111111111111111111111111 \
  --q infinity --r 3 --a 1,2
./scripts/check.sh
./benchmark.sh
python3 scripts/run_hostile_fixtures.py
# Slow, official-baseline-only regression:
python3 scripts/check_seeded_oracle.py --artifact-regression
```

`run-case` times the exact protected seeded-oracle garble and then
`evaluateWithLabels`. The release verifier tests both nonzero `Q` and
`Q = infinity`, uses a full-width scalar and valid `A`, compares against the
protected G1 computation, enforces the proved byte bound, and measures peak
RSS externally. The optional official-baseline regression holds the hidden
input and test labels fixed while checking that distinct internal seeds change
the artifact digest. `benchmark.sh` performs the same work in a fresh local Lake
project and records a non-authoritative result with the protected/submission
digests and pinned dependency revisions.

## License

Licensed under the [Apache License 2.0](LICENSE).
