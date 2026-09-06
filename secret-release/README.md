# SecretRelease

A shared, construction-independent contract for known-input conditional secret
release. The mathematical rule is [one file](SecretRelease.lean); runtime code,
transport laws, examples and tests are separate. See [ARCHITECTURE.md](ARCHITECTURE.md)
for the implemented tool protocol and ownership map.

The library does not prescribe gates, half-gates, fields, artifact layouts or
hash usage. It includes Lamport, HORS, OnesOnly, Preimage, Plain and
`ClassicalBoundedQueryROM`. Construction/security reductions belong in solutions
or optional proof libraries, not this contract.

## Author a challenge

Require the shared Lake package and define a `Challenge` with its reference,
private/input codecs, disclosures, forbidden claim, permitted leakage and ROM
bound. A codec includes both round trips; checked subtypes express on-curve,
checksum and other validity preconditions. Invalid encodings are outside honest
correctness, never a restriction on the attacker's computations.

Add a `WireFormat challenge` with an identity and canonical key codecs. Built-ins
supply `.lamport`, `.hors`, `.onesOnly`, `.preimage` and `.plain` key adapters.
The full output-value codec is optional. Custom disclosures can be variable-size
and depend on the oracle; they supply a `ByteCodec` for their finite key space.
Private/input wire encodings come from their mathematical bit codecs, including
zero padding for non-byte-aligned widths.

```lean
import SecretRelease.Runtime
-- For a challenge c with Lamport inputs and plaintext encoded output:
-- def wire : WireFormat c where
--   identity := "my-challenge-v1"
--   inputs := .lamport inputCodec
--   outputs := .plain encodeOutput
--   output := some outputCodec.bytes
```

The working examples are [G1's declaration](../g1-release/G1Release/Protected/Target.lean)
and [BLAKE3's declaration](../blake3/Blake3Prize/Protected/Challenge.lean), with
adjacent `Wire.lean` files. A new author supplies mathematics and short Rust
reference tests; shared code supplies the executable handlers and verifier.
Register the protected module names in `challenge.json` and project name in
`secret-release/challenges.json`. Lake needs one generated `SRTools` target;
there are no author-written `main` functions or per-challenge CI workflows.

## Runnable candidates and certificates

`Scheme c` chooses its artifact type, coin count, garbler, artifact codec and
evaluator. A submission exports `Option (Candidate c)`. A candidate contains
`scheme`, `maxBytes` and `certificate : Option (Certificate scheme maxBytes)`.
Use `none` for the certificate while implementing/proving a construction.

A full certificate requires serialized correctness (or the author-fixed
statistical correctness error), both artifact-codec laws, universal byte size,
post-release claim security and every enabled withholding/private-map goal.
The certificate is indexed by the exact executable scheme and byte bound.
`Candidate.certified` produces an optional complete `Certified` bundle.

Missing and uncertified entries have **no accepted score**. Their `score.txt`
remains `unranked`; only an audited complete certificate permits a numeric score.
Executable tests never become a security assumption. `SizeAccepted c limit`
can additionally enforce an author-owned hard cap.

## Four tools and Rust tests

```sh
python3 secret-release/scripts/bundle.py blake3
blake3/.yukon/bundle/challenge describe
python3 secret-release/scripts/test_rust.py blake3 blake3/.yukon/bundle
```

The bundle always provides `garble`, `encode`, `evaluate`, and `challenge`.
`encode` applies the input codec and the actual disclosure's `reveal`, then
writes canonical known input plus selected labels. A missing candidate still
supports `encode` and protected reference commands. `garble` receives no
plaintext input; `evaluate` receives no private parameters or full key sets.
See the [file argument table](ARCHITECTURE.md#generated-tools).

The [Rust SDK](rust/secret-release/src/lib.rs) handles process/file I/O,
status/binary hashes, fixtures, label selection and measurements. Author tests
compare the generated reference and actual binary pipeline with an independent
library. G1 uses Arkworks; BLAKE3 uses the official `blake3` crate. Custom outputs
without a value codec can be tested with expected released bytes directly.
Seeded fixtures are public test data. The tools accept supplied keys/coins;
`Finite Keys` is not silently treated as a production randomness generator.

The initial runtime uses shared trusted C SHA-256. Compiler/FFI trust is explicit;
**instantiating the ideal oracle with SHA-256 remains heuristic and unproved**.
The theorem does not assume that collision/preimage resistance makes SHA-256 an
ideal oracle. The proof import graph excludes this executable primitive.

## Security model and limits

The author fixes the rule before submissions. Secret keys are uniform on the
finite nonempty disclosure spaces, independent between inputs and outputs and
independent of coins and the shared random function. Lamport's two labels are
distinct within each pair; cross-coordinate collisions remain possible.

The evaluator knows the static input and receives its selected input and output
disclosures for free in the post-release game. The adversary can compute
arbitrarily but has a worst-case bound on classical oracle queries, expressed
using pinned VCVio `OracleComp` and `IsTotalQueryBound`. Both challenges require
error at most `(q+1)/2^128` for every `q ≤ 2^64`.

Lamport reveals one label per bit; OnesOnly reveals a uniformly random secret
only where a bit is one; HORS uses an author-fixed possibly hash-dependent
selector; Preimage releases one secret conditionally; Plain releases encoded
public output. For credential unforgeability, `wins` must test a **different
valid credential**, not merely every unrevealed raw component. Ones-only
credentials can disclose subsets: shape/checksum validity must express the
intended authorization. An attacker is always allowed invalid intermediate
values. `wins` determines which final claims count.

Post-release whole-label recovery does not establish pre-release withholding,
absence of partial leakage, input hiding, adaptive/multiple releases, malicious
construction security or side-channel resistance. Enable the separate
withholding predicate when needed. Private-map privacy compares ordered pairs
with equal explicitly permitted leakage; this is not a bounded-simulator theorem.
The optional `SecretRelease.Simulation` facade exposes pinned VCVio UC and cost
infrastructure but adds no proof or security assumption by itself.

The current ROM profile intentionally excludes relying solely on computational
hardness against unlimited local computation. Future reviewed profiles may
reuse the disclosure interface with a properly bounded adversary/cost model.
A candidate may not choose its own security assumptions or adversary class.

## Trust and resource limits

All required instance-dependent public state belongs in the scored artifact.
Only fixed program code and declared disclosure channels are outside that score.
Specializing a free binary with private instance data is not permitted. Bundle
size and native channel/artifact measurements are reported separately.

Shared CI verifies immutable-base ownership, source policy, dependency pins,
fresh local-source compilation, exact certificate types, canonical transport,
allowed axiom closure, negative certificate cases and the actual binaries.
`protected.sha256` establishes consistency only; the full Git-tree admission
check authenticates the base-owned rules. Rust code, tests, pins, registry,
workflow and runtime descriptors are protected. Authoring previews never rank.

Builds/tests are sequential: **8 GiB CI / 4 GiB local** aggregate build RSS,
**1 GiB native**, one Lean/Cargo thread, nice 10, with time/process/output/disk
limits. Never set `GITHUB_ACTIONS=true` locally. Use the shared scripts rather
than naked Lean, Lake or Cargo test invocations.

The original root G1 ideal-pad challenge remains separate. Its 5,940,480-byte
bound is not a shared finite-key ROM certificate. The runnable BLAKE3
707,680-byte half-gates baseline likewise still lacks its complete certificate.

CI publishes `bundle.tar.gz`; extract it with `tar -xzf bundle.tar.gz` and set
`SECRET_RELEASE_BUNDLE` to the resulting `bundle` directory. The tar preserves
executable permissions and shared hard links, which raw CI file uploads lose.
