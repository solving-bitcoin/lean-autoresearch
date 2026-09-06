# SecretRelease architecture

The original plan is implemented as a shared mathematical contract, canonical
byte/key adapters, generated tools, runnable candidates, a Rust SDK, and a
shared verifier/CI workflow. This document describes the resulting interfaces.
No complete finite-label ROM certificate is claimed for either current entry.

## Mathematical contract: one file

`SecretRelease.lean` contains `Codec`, `Disclosure`, Lamport, HORS, OnesOnly,
Preimage, Plain, `ClassicalBoundedQueryROM`, `Challenge`, `Scheme`, correctness,
serialized size, security games, and certification. It imports neither a
construction nor an executable hash backend.

`Certificate scheme maxBytes` contains every existing obligation: exact or
reviewed statistical correctness, both artifact-codec laws, universal byte
bound, post-release security, optional withholding, and optional equal-leakage
private-map privacy. `Candidate` contains the executable scheme and byte claim
plus an optional certificate indexed by those exact values. `Certified` is the
complete scheme/bound/proof bundle. Missing proofs are represented by `none`,
never `sorry`, new axioms, or submission-chosen assumptions.

The initial ROM allows unlimited local computation and bounds classical oracle
queries. It is not a computational-hardness profile for arbitrary PRF/lattice
assumptions, not a multiple-release guarantee, and not a simulation theorem.
The VCVio simulation/cost facade stays optional and does not add an obligation
to the certificate merely by being imported.

## Byte boundary and runtime

`SecretRelease/Encoding.lean` derives canonical byte encodings from fixed bit
codecs, including non-byte-aligned widths. Bit order is byte-major LSB-first;
unused padding must be zero. It supplies product, finite-function and subtype
codecs and key encodings for every built-in disclosure. A `ByteCodec` includes
both round-trip laws. Custom disclosures provide their own codec.

`SecretRelease/Runtime.lean` provides `WireFormat challenge`, `KeyWire`, and pure
adapters. A full reference-output codec is optional: arbitrary output types and
custom variable-size/hash-dependent disclosures remain eligible. The library
proves the adapters agree with the mathematical garbler, reveal functions,
serialized evaluator and reference, including the complete honest pipeline.

`SecretRelease/CLI.lean` owns all command handlers. `NativeHash.lean` and
`native/sha256.c` supply the initial trusted C SHA-256 runtime profile. The
ideal-ROM/SHA-256 bridge remains explicitly heuristic and unproved.

## Generated tools

`python3 secret-release/scripts/bundle.py g1-release` (or `blake3`) generates the
Lean entrypoint from protected identifiers, builds it once, and packages four
entrypoints. Authors write no `main` functions. The files share an inode where
supported; each filename selects one fixed command role. Bundle metadata records
all four hashes and both unique installed bytes and unpacked tool bytes.

| Tool | File arguments, in order | Result |
| --- | --- | --- |
| `garble` | coins, private value, input keys, output keys, artifact destination | Complete submission-owned artifact |
| `encode` | input, input keys, known-input destination, active-label destination | Canonical known input and `inputs.reveal` |
| `evaluate` | artifact, known input, active labels, output destination | Released output bytes |
| `challenge reference` | private value, input, output destination | Encoded full reference value, when a codec exists |
| `challenge release` | encoded output value, output keys, destination | Selected output disclosure |
| `challenge expected` | private value, input, output keys, destination | Reference disclosure, including custom outputs without a value codec |
| `challenge roundtrip` | kind, source, destination | Canonical private/input/output/input-keys/output-keys bytes |
| `challenge sha256` | source, destination | Runtime SHA-256 result |
| `challenge describe` | none | Identity, widths, key formats, candidate/certificate status, primitive profile |
| `challenge bound` | query count | Exact rational error bound and whether the count is admissible |

`garble` never receives the plaintext input. `encode` receives no private
parameters or output keys. `evaluate` receives neither full key set. Known input
and active disclosure are separate files because the challenge already declares
these channels. No extra instance-dependent public state is allowed there.
The submission controls the complete artifact format; there is no mandatory
artifact header. Fixed tool bytes are reported separately from per-instance size.

An absent candidate still permits `encode` and reference operations. An
uncertified candidate can execute every tool. Only a kernel-audited complete
certificate plus trusted provenance and successful native tests permits ranking.
Packaging alone always sets `acceptance: not-audited` and `score: null`.

## Rust tests

The pinned Rust workspace is `secret-release/rust`. `secret-release` is the SDK;
challenge test crates use it with independent reference libraries. The SDK owns
role-specific file/process calls, temporary files, exit/timeout handling, binary
hash checks, deterministic fixtures, selected-label comparison, and artifact
measurement. Custom keys can be supplied through `Fixture`; custom output
formats use `assert_released` instead of requiring a built-in Rust enum.

```rust
#[test]
fn hash_release() -> secret_release::Result<()> {
    let bundle = secret_release::Bundle::from_env()?;
    let message = [42u8; 64];
    let fixture = bundle.test_fixture(&[], &message, 7)?;
    bundle.assert_case(&fixture, blake3::hash(&message).as_bytes())?;
    Ok(())
}
```

Run through `python3 secret-release/scripts/test_rust.py PROJECT BUNDLE`.
Cargo compiles once with `--locked --jobs 1`; produced test executables run
sequentially under the separate native cap, including their child tools. The
SDK has per-call time/output limits; the shared test runner supplies aggregate
RSS, process and disk enforcement. Calling the Rust tests directly bypasses
that outer resource guard and is not the supported verification path.

Seeded fixture keys are public test data, not production key generation or a
proof of the uniform law. Runtime production key generation is deliberately
not inferred from `Finite Keys`; callers supply keys and coins. No claim about
OS randomness is silently added to the mathematical contract.

## Challenges and migration

G1 uses the shared contract directly: private canonical `(Q,r)`, valid affine
`A`, 512 Lamport input bits, canonical plaintext `Q + [r]A`, opposite-input-label
recovery, and equal-result private-map privacy. Its entry is absent; an explicitly
insecure transport fixture is used to test all roles. Arkworks independently
checks 21 arithmetic cases, canonical encodings, cancellation and infinity.

BLAKE3 now accepts `SecretRelease.Certificate`, specialized in
`Blake3Prize/Protected/Challenge.lean`. It keeps the original GF(2) reference,
512 input pairs, 256 output pairs, known message and post-release opposite-label
game. Withholding is not added. Its executable half-gates baseline is ported
from the existing Python implementation and is runnable but uncertified, with
a 707,680-byte claim. The official Rust BLAKE3 crate checks the reference and
selected-output pipeline. Gate proofs alone do not certify this candidate.

`Blake3Prize/Migration` retains historical definitions exclusively for migration
evidence, outside the accepted import graph. Checked transport covers the
768-pair law versus two independent uniform key spaces, unchanged coins/oracle,
bit/label order, public views, winning rule and query bound. Legacy bounds on
all pair functions imply bounds on the new valid distinct-pair domain. Invalid
pairs are no longer values of the key type; they are rejected by the wire codec.
The old root G1 ideal-pad challenge remains separate.

## Ownership and CI

Protected `challenge.json` selects fixed modules/identifiers, audits, reference
tests and report names. `secret-release/challenges.json` registers projects for
both shared workflows. The mathematical reference and bespoke codecs remain
real author work; a Rust reference library cannot replace them or prove secrecy.

The shared verifier rebuilds local protected sources in isolation, reuses only
authenticated pinned external Lean caches, runs source/axiom/negative-certificate
checks, builds fixtures and candidates, tests their actual bundles, and writes
rank/status metadata. Rust manifests, lockfile, tests and SDK are protected too.

`secret-release-submission.yml` runs the immutable base's code. The head tree is
read only as Git blobs; changes outside registered submission files fail before
any candidate execution. Candidate digests cannot authenticate modified rules.
Authoring previews are separate and always have a null accepted score.

All work is sequential: local builds have a 4 GiB aggregate RSS cap, GitHub
builds 8 GiB, and native tests 1 GiB. Never set `GITHUB_ACTIONS=true` locally.

CI publishes `bundle.tar.gz`; extract it with `tar -xzf bundle.tar.gz` and set
`SECRET_RELEASE_BUNDLE` to the resulting `bundle` directory. The tar preserves
executable permissions and shared hard links, which raw CI file uploads lose.
