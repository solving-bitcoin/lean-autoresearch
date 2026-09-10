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

## Active challenges

Both challenges minimize a universally proved serialized artifact byte bound
under the shared [SecretRelease contract](secret-release/README.md). Each has
its own Lean project, protected boundary, submission directory, and verifier.

### BLAKE3 labeled hashing

The [BLAKE3 challenge](blake3/README.md) covers a 64-byte input and 32-byte digest,
with independent 32-byte label pairs on every input and output bit. The evaluator
knows its plaintext message and obtains the selected output labels while
protecting all 768 opposite input/output labels.

```bash
./blake3/setup.sh
./blake3/benchmark.sh
```

### BN254 G1 conditional release

The [G1 release challenge](g1-release/README.md) covers the private affine map
`A ↦ Q + [r]A` on BN254 G1. The evaluator knows the finite-affine point `A`,
receives 512 active input labels, and obtains the canonical plaintext output.
Submissions prove correctness, exact codec laws, a universal byte bound,
opposite-label secrecy, and private-map privacy.

```bash
./g1-release/setup.sh
./g1-release/benchmark.sh
```

Run one challenge at a time. These scripts enforce a 4 GiB local aggregate build
RSS cap, a 1 GiB native RSS cap, and one Lean thread. For changes to protected
rules, use `--authoring-preview` with the relevant benchmark script. Authoring
previews do not accept ranked scores; trusted submission verification uses the
immutable base revision.

Both challenges use a ClassicalBoundedQueryROM proof profile on Lean 4.33.1.
The concrete SHA-256 instantiation remains heuristic. See the
[shared architecture](secret-release/ARCHITECTURE.md) for the generated tools,
security model, and verification process.

## License

Licensed under the [Apache License 2.0](LICENSE).
