# Direct-base-16 WOTS to fixed Lamport labels

**Experimental authoring track; unranked; full Lean validation is pending.**
The candidate has `certificate := none` and `score.txt` contains `unranked`.
This is a research implementation and test harness, not a completed
cryptographic certification. See [PROOF_STATUS.md](PROOF_STATUS.md).

The reference is identity on **all 32-byte messages**. Before seeing a message,
`Prepare(keys, fixed_labels, coins)` builds one artifact. Later, a canonical
WOTS signature enables `Expand` to recover the supplied label for each of the
256 message bits. Labels are never redefined or derived from message hashes.
Correctness is intended for every distinct-pair label table. The security
experiment independently samples the built-in Lamport key space, WOTS seeds
and coins uniformly; this is not a shared-XOR-offset GC label distribution.

## Frozen first profile

The source inspected was [bitcoin-scripts at
bf9ee0bb34987a9130ad9dc13a06e18fef137296](https://github.com/solving-bitcoin/bitcoin-scripts/tree/bf9ee0bb34987a9130ad9dc13a06e18fef137296),
specifically `src/signatures/winternitz/base16/mod.rs` and the shared chain hash
and preimage modules. Starter attachments were not supplied or read.

| Parameter | Choice |
| --- | --- |
| Intended verifier | `FastWinternitz<32, Sha256, FullWidth>::checksig_verify` |
| Message | 32 original bytes, high nibble then low nibble |
| Message chains | 64, maximum digit 15 |
| Checksum | `960 - sum(message_digits)` |
| Checksum coordinates | low-first radices 8, 8, 16; maxima 7, 7, 15 |
| Chain step | SHA-256 on the full 32-byte previous node; identity endpoint commitment |
| Model key | 67 independently uniform 32-byte starts |
| Upstream key | 32-byte master seed with deterministic namespace/index derivation |
| Canonical raw witness | 67 `[minimal ScriptNum digit, 32-byte node]` pairs |
| Active byte channel | 67 nodes in coordinate order, 2,144 bytes |
| Known message channel | 32 bytes; supplies canonical selectors |
| Output byte channel | 256 selected labels, 8,192 bytes, byte-major LSB-first |

The strict exact-hash verifier was chosen, not the clamped or width-relaxed
size verifier. Its canonical signer uses `to_witness`, not
`to_size_optimized_witness`. The Rust adapter intentionally accepts only
canonical raw selectors and exactly 32-byte nodes. It is **not** a complete
Bitcoin interpreter or a characterization of all Script-accepted aliases.
`EncodedMessage`, `AcceptedWord`, semantic witness and raw witness are distinct
Lean types. The Script correspondence theorem remains open.

For output bit `i`, the source nibble is `2*(i/8)+1` if `i%8<4`, otherwise
`2*(i/8)`; its bit within that nibble is `i%4`. Tests cover every bit position
at every possible checksum total. No 160-bit digest or enumerative message
encoding is introduced, so unused ranks are not applicable to this track.

The ROM model is deliberately different from upstream's master-seed law and
the default HASH160/16-byte-start profiles. SHA-256 is an executable heuristic
instantiation of the ideal oracle. No equivalence or concrete-hash security
theorem is claimed. FullWidth chain semantics match the inspected source at
the formula level. Three selected tests in the unmodified pinned upstream
checkout also passed through its patched Script interpreter. This is neither
a formal correspondence theorem nor a Bitcoin Core consensus/policy result.

## Weighted threshold construction

The direct code is not an ordinary fixed-sum code: checksum carries change
the unweighted sum. It does have the exact weighted relation

```
sum(message_digits) + c64 + 8*c65 + 64*c66 = 960
sum_j weight[j]*maximum[j] = 1983
T = sum_j weight[j]*(maximum[j]-digit[j]) = 1023
```

This permits a weighted specialization of the supplied microchallenge without
switching the first track. For each message bit and each label value, take an
independent polynomial for every 16-bit limb of that fixed 32-byte label. The
constant coefficients are those 16 limbs in `F_65537`.

At each nonpublic node `k<D_j`, publish `weight[j]` encrypted evaluations.
On the target message coordinate replace that multiplicity by
`weight[j] + f(k) - f(k+1)`, where `f` tests whether the target bit equals the
label value. This is integer arithmetic; multiplicity is 0, 1 or 2 on a message
coordinate. Repeated slots have DIFFERENT nonzero evaluation points and mask
domains. No public endpoint encrypts a share.

Starting from a signature, the evaluator obtains the full forward closure.
The exposed count telescopes to

```
T - f(D_i) + f(c_i) = (T+1-f(D_i)) - 1 + f(c_i).
```

For value 0 the threshold is 1,024 and there are 1,984 public evaluations.
For value 1 the threshold is 1,023 and there are 1,982 public evaluations.
Each evaluation holds 16 field elements, three little-endian bytes each.
All coordinates are distinct in 1..1984, below the field characteristic.
Interpolation is at zero; noncanonical field elements are rejected. A
reconstructed limb must be below 65,536 for lossless label decoding.

The first 32 coin bytes are a public setup nonce. Each nonconstant coefficient
uses its own independent 32-byte coin block, reduced modulo 65,537; value-1
polynomials leave the final block unused. This sampler is not exactly uniform:
`2^256 mod 65537 = 1`. A single coefficient has total variation distance
`65536/(65537*2^256)` from uniform. The joint proof must account for every used
coefficient. Tests of toy Shamir distributions do not prove this reduction.

Every share is XOR-masked by 48 bytes from two domain-separated oracle calls.
The domain includes a fixed tag, nonce, entire public key, output wire, label
value, unique evaluation coordinate, chain node and block number. Each label
has a separate domain-separated public commitment. These commitments add
oracle targets; they are not a substitute for the withholding/security proofs.
The implementation checks commitments after interpolation, including when a
caller bypasses the official extraction path in the independent tests.

The research inspiration is [Sergeevitch et al., ePrint
2026/1684](https://eprint.iacr.org/2026/1684). Its abstract was accessible;
PDF retrieval was denied, so no unseen end-to-end proof is relied on. The
weighted specialization above is an implementation proposal derived from the
supplied specification and inspected checksum, not an attribution of a
checked theorem to that paper.

## Scored public data

| Region | Bytes |
| --- | ---: |
| Public key (author wrapper) | 2,144 |
| Setup nonce | 32 |
| 512 label commitments | 16,384 |
| 256 × (1,984+1,982) evaluations × 48 bytes | 48,734,208 |
| **Candidate claim** | **48,752,768** |

The candidate consumes 268,173,344 coin bytes. Secrets and coins are private
setup inputs, not unscored public instance data. All tables, decoding material,
nonce and commitments are in the artifact. Fixed executable code is shared.
The label/key/coin fixtures in tests are deterministic public test data, not
production key generation. The universal Lean `Layout.artifact_bound` theorem
checks this byte bound; it does not establish correctness or security.

The protected `Construction` wrapper always prefixes the actual public key to
the scored artifact. `Entry` can only produce a shared `Candidate` using this
wrapper, and the candidate audit requires that exact mapping. Both pre- and
post-release games therefore expose the public key, not merely the verifier
used inside Expand. The raw byte artifact codec is identity/some; malformed
body lengths and encodings are rejected by evaluation.

## Security and protocol boundary

The post-release game gives an arbitrary bounded-query attacker the public
artifact, message, complete canonical signature AND selected labels. It wins
by recovering any opposite output label. Withholding is also required: before
release, recovering either label at any wire wins. Both games allow arbitrary
local computation and arbitrary decoding algorithms.

The author-owned numerical target is
`2^20 * (q + 2^32 + 1)^2 / 2^256`, for `q <= 2^48`. The `2^32` honest-query
budget and `2^20` multi-target allowance are deliberately explicit. This is a
nontrivial acceptance target, not a derived bound. The joint proof must account
for all 67 chains, seeds, endpoints, masks, label commitments, setup queries,
collision events and coefficient bias; it may reveal that this target needs
author review. No candidate is currently certified against it.

`Protected/Adaptive.lean` separately models artifact-first adaptive message
selection followed by exactly one release and a second adversary stage. The
static certificate does not imply it. Simulation/indistinguishability for GC
composition, shared-XOR-offset labels, malicious setup and all raw accepted
Script witnesses are NOT proved or claimed. No simulation certificate type is
invented with competitor-selected assumptions.

Signing twice breaks the intended boundary. The tested pair of all-zero and
all-ff messages reveals every seed; a caller can then recover both labels and
sign arbitrary third messages. One-key lifetime enforcement is an application
obligation, not a property of stateless test helpers.

Nonce/pk/label commitments help detect mismatched prototype inputs under the
concrete hash. They do not bind a GC identity, transaction or external label
commitment scheme without an explicit protocol. The nonce is not an
authenticated GC identifier. A hash commitment does not ensure availability;
an off-chain decoder returning `none` is not an enforceable Bitcoin fraud
proof. This repository addition does not implement a complete fraud protocol.

## Validation

```sh
# Installed Rust lives outside the repository in this cloud environment.
source /workspace/toolchains/env.sh
python3 wots-lamport/scripts/check_local.py
python3 wots-lamport/scripts/check_local.py --full-reference

# Required when Lean becomes available through permitted installation:
./wots-lamport/setup.sh
./wots-lamport/benchmark.sh --authoring-preview
```

`check_local.py` runs policy/integer checks, a locked single-job Rust build and
guarded native reference tests. It explicitly skips the generated-Lean-tool
test; the normal shared verifier never skips that test. Full-size reference
testing prepares one artifact before choosing three later messages. Reusing a
key there is a correctness experiment, not a security experiment.

Negative tests cover absent/incomplete signatures, full forward closure,
checksum carries, public endpoints, mixed keys, selector aliases rejected by
the canonical adapter, invalid widths/digits, duplicate interpolation points,
wrong nonce/commitment/artifact and two-signature misuse. Actual raw Script
acceptance and full malicious-setup properties remain separate open work.

All builds/tests retain the existing sequential resource guards: 4 GiB local
build RSS, 1 GiB native RSS, one Lean thread, nice 10, five-minute native cap.
The full generated pipeline additionally retains the SDK's 60-second per-tool
limit. Performance under that limit has not been established for Lean.
Authoring previews never emit ranked scores. Trusted acceptance uses the
immutable base, so this new protected track must be reviewed and merged before
any submission could be accepted. The work is published for review in draft
PR #6; no ranked submission or merge has been performed.

## CI cache and draft review

Authoring preview runs on draft PRs and has read-only cache access. Only the
main-branch trusted-cache workflow saves external dependency caches. The first
PR is consequently a cold build; a producer added by this PR cannot run from
main until the workflow is reviewed and merged. No merge is authorized here.
Keys bind platform, toolchain, manifests, verifier version and protected source
digest. Exact hits must pass source, compiled-byte and Lake-configuration checks
before Lake runs. Partial hits are deleted; invalid exact hits fail closed.
Protected/local modules are always rebuilt in the isolated verifier tree.
The seal is an integrity check, not a signature; writer provenance is enforced
by GitHub cache scopes, read-only consumer tokens and the main-only producer.
A green preview does not certify or rank this reference candidate.

## Packed coin execution

The mathematical scheme still quantifies over every `Bytes randomnessBytes`
coin string, with the same independent byte law. `PackedGarble` offers an
optional runtime implementation on packed `ByteArray` inputs, accompanied by
an `agrees` proof for every valid coin string. The shared entrypoint checks the
exact length before selecting it. WOTS's wrapper uses this path to avoid the
2 GiB pointer array that unpacking its 268 MB coin buffer would otherwise
require on a 64-bit host. Existing schemes default to the original path.
This changes representation only: no entropy expansion, smaller random seed,
new oracle assumption, relaxed certificate or larger resource limit is used.
The shared `garblePacked_eq` correspondence theorem and large-buffer native
regression passed hosted validation at `50e6007`. This representation result
does not establish the WOTS executable's performance or security.

Author preview checks ready dependency layers in one Lake invocation to reduce
graph startup overhead, retaining one Lean thread and the same single author
time cap. Ordinary failures are rechecked per target; resource failures stop
immediately. Run 59 checked 112 of 120 modules; its author cap expired during
executable building. Run 57 passed generated lane SDK integration and full
independent reference-artifact/later-message correspondence within the same cap.
Two source failures block six dependent modules and the complete security proofs.
There is no security certificate.
See [PROOF_STATUS.md](PROOF_STATUS.md) for exact evidence and outstanding work.

Runtime phase evidence is retained atomically across an outer timeout. It is
diagnostic only: a started SDK or correspondence check is never reported as
passed, and all original proof and native acceptance gates remain required.
