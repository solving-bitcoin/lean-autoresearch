# Proof and validation status

The candidate remains **uncertified and unranked**. The pinned compiler is
Lean 4.33.1. Source declarations count as proved only after that compiler
accepts them; Rust/Python tests are independent validation, not Lean proofs.
`Submission.submission.certificate = none` and `score.txt = unranked`.

## Compiler-checked results

The following modules passed hosted Lean elaboration. This does not mean the
complete imported submission or its security certificate passed.

| Result | Checked modules | Evidence commit |
| --- | --- | --- |
| All 256-bit messages, encoding round trips, canonical signing and forward closure | Protected.Encoding, Chains, Disclosure, ScriptRelation, Challenge, Target, Wire | `a2dce49` |
| Nonvacuous games and separate artifact-first adaptive game | Protected.Adaptive, Tests.Contract, Tests.RunnerFixture, Tests.Nonvacuity | `18aebd8`, `d048390` |
| Packed-coin execution equals mathematical vector execution | shared Runtime.garblePacked_eq | `50e6007` |
| Exact bit mapping and executable inversion | BitMapping, InverseBridge | `d67ce75` |
| Weighted sum 960 and remaining depth 1023 | Geometry | `80d2a99` |
| Polynomial degree, constant term and modular Horner interpretation | FieldBridge | `6f344d2` |
| Universal artifact bound of 48,752,768 bytes | Layout.artifact_bound | `e65c736` |
| Exact selected/opposite share counts, distinct nonzero visible coordinates | Exposed | `e65c736`, `00cc333` |
| Executable interpolation equals exact field/natural reconstruction | InterpolationBridge | `6531e8e` |
| Share-byte round trips, mask cancellation and table-row extraction | ByteBridge | `00cc333` |
| Prepared commitment/share slices and lossless label repacking | ArtifactBridge, LabelBridge | `8b06ee6` |
| Abstract Shamir secret-shift bijections and joint uniform-polynomial privacy | Shamir, ShamirLaw, VisiblePrivacy | `f605fb5`, `00cc333` |
| Exact 256-bit modular residue fibers and marginal probabilities | SamplerLaw | `8b06ee6` |
| Byte/integer bijection and actual single-block decoder law | CoinEncoding | `3e17ad3` |
| Coefficient-vector/polynomial equivalence and joint coefficient privacy | PolynomialLaw | `3e17ad3` |
| Padded/selective polynomial privacy, exact coefficient-list encoding and marginal mixture | PaddedPolynomialLaw, PolynomialEncoding, SamplerMixture | `3d1bcb3` |
| Every honest table row decrypts to its exact field shares | DecodingBridge | `3d1bcb3` |
| Executable weighted-sharing construction after expansion refactor | Sharing | `6531e8e` |

## Current validation attempt

Hosted run 33 at `e959f9e` exceeded the unchanged 1,800-second author-check
limit. The timeout path discarded its captured source/runtime output, so no
additional module or native pass is inferred. Cleanup showed a Rust reference
test process had started. This does not identify the original SDK failure.
The next batch preserves bounded timeout diagnostics, prints explicit module
and runtime stages, and narrows tactic imports. It keeps the original
executable and every resource limit unchanged.

Hosted run 32 at `3d1bcb3` failed the complete WOTS source build. It checked
PaddedPolynomialLaw, PolynomialEncoding, SamplerMixture and DecodingBridge.
The remaining direct errors are in CoinBlocks, DomainSeparation, Expansion,
OracleSupport and VisibleCoefficientPrivacy; their dependents remain blocked.
The next batch adds explicit finite indices/query syntax, controlled slice
arithmetic, noncomputable distribution declarations and expansion repairs.
Scoped recursion depth 4096 permits the 256-element expansion conversion;
heartbeat, RSS and process time limits are unchanged.

The authoring-only runtime diagnostic successfully built SRTools and packaged
the four generated tools. Its supplied-bundle integration test failed after
64.27 seconds with the SDK's combined timeout/side-output error. This is a
real runtime failure, not acceptance. The SDK diagnostic now names the tool,
elapsed time, timeout flag, output-overflow flag and side-output byte counts,
without changing any limit. The candidate executable remains unchanged while
that failure is isolated. It still has no certificate and `not-audited`
metadata; the diagnostic cannot create acceptance or an exported archive.

Additional source work connects finite oracle restrictions to VCV's lazy
random-oracle semantics, preserves query budgets, counts guesses against the
actual distinct-label-pair space, and proves deterministic chain-table and
mask-domain properties. Generic coupling lemmas retain their explicit
premises. These are proof attempts, not assumptions admitted into a candidate
certificate; none substitutes for the actual joint reduction.

`MachineHorner` is a further unchecked optimization proof attempt. It defines
a tail-recursive UInt32 evaluator, proves the intended no-overflow step and
states exact correspondence for arbitrary coefficients at coordinates at most
1984. It is imported for audit but is not used by the current executable.
No performance improvement is claimed before compilation and measurement.
`MachineSharing` extends the attempted correspondence to every prepared byte
and the whole construction. `MultiTargetTrace` removes mutual independence
from the targets' union bound, while retaining independence of their baseline
view. `MaskedViewLaw` attempts the joint coefficient/pad bijection preserving
ciphertexts and visible pads. These modules are unchecked, and the executable
still uses the original construction.
`ChainCollisionLaw` attempts an explicit uniform-table fiber count and the
1,056-position ideal-tape collision bound. It does not supply the missing
real-chain coupling. Broad tactic imports are being replaced by the specific
tactics in use; this also awaits Lean validation under the same build cap.
`MachineFieldReduction` separately attempts exact UInt32 Fermat-prime
reduction. It is not used by the evaluator or candidate.

## Obligations still open

| Obligation | Remaining work |
| --- | --- |
| Universal honest correctness | Check Expansion through `construction_correct` for the exact protected wrapper |
| Complete coefficient law | Check independent byte blocks, allocated/padded coefficient tables, raw nonce and two-sided joint sampling-error bounds |
| Joint visible-share privacy | Check the full sampled coefficient-table specialization, including all 16 limbs and all 512 labels |
| Actual oracle programs | Check reification, measurable winning events and the honest query budget |
| ROM reduction | Establish the real/ideal joint laws and bound chain collisions, hidden-node queries, mask/commitment programming and label guessing |
| Pre-release withholding | Prove `ROM.WithholdingSecure` against every bounded-query program |
| Static post-release security | Prove `ROM.ReleaseSecure` with the selected labels supplied for free |
| Adaptive message choice | Prove the separate artifact-first two-stage `AdaptiveSecure` theorem |
| Native implementation | Run generated Lean tools and byte-for-byte reference correspondence within all unchanged caps |
| Certificate | Fill every field with checked proofs, run isolated source/axiom audits and validate the final bundle |

## Fixed numerical target

The author-owned target is `2^20 * (q + 2^32 + 1)^2 / 2^256`, for
`q <= 2^48`. Its nontriviality is checked, but this is not a security reduction.
The accounting must cover 67 correlated chains (989 endpoint steps), 512 label
commitments, 1,015,296 encrypted evaluations with two mask queries each,
8,380,416 allocated coefficient blocks, the raw nonce, and all adversarial
queries. Repeated calls count again. The scalar sampler is biased because
`2^256 mod 65537 = 1`; no exact-uniform-sampler assumption is allowed.

The direct 67-chain profile has weighted remaining depth 1023. It is not
replaced by the excluded fixed-sum T=0 singleton or an enumerative 66-digit
laboratory.

## Independent evidence and boundaries

The independent Rust implementation and Python arithmetic/format/boundary
tests pass. They do not prove the candidate. Hosted run 32 measured Rust Prepare at 19.23 seconds, the full fixed-artifact
three-message test at 26.51 seconds, and peak RSS at 320,348,160 bytes.
This does not predict Lean timing.

The pinned Script comparison is reproduced in [BITCOIN_COST.md](BITCOIN_COST.md):
maximum complete-spend sizes are **2,101 vbytes WOTS** and **7,209 vbytes
Lamport** for the matched SHA-256/full-width profiles and stated transaction
fixture. The offchain artifact is 48,752,768 bytes. Bitcoin Core retrieval was
denied by proxy 403; no Bitcoin Core consensus or relay-policy result is claimed.

Canonical signing, every raw Script witness, simulation/GC composition,
malicious setup, authenticated transaction/label binding, availability, and a
Bitcoin-verifiable fraud protocol are distinct statements. They are not
implied by the current construction or the intended static ROM certificate.
The protected seed distribution uses independent seeds, not the upstream
master-seed derivation.

## Reproducibility and resource limits

Local Lean installation was denied by proxy 403 and was not bypassed. The
compiler runs in the authorized hosted workflow. Builds are sequential with
one Lean thread and nice 10: 4 GiB locally, 8 GiB in CI. Native processes retain
1 GiB RSS; native suite limits are 300 seconds locally and 600 seconds in CI,
with the SDK's separate 60-second limit for each generated tool unchanged.

Two earlier source builds exceeded the unchanged 8 GiB cap. Sequential builds
and symbolic geometry replaced parallel elaboration and full slot enumeration;
no cap increase or native evaluation axiom repaired those failures.

The unchanged local verifier regression suite requires a temporary child-reaping
supervisor because this container's PID 1 leaves killed descendants as zombies.
The supervised suite passes; no repository guard was weakened to hide this.
Hosted BLAKE3 and G1 previews at `50e6007` passed, including packed-runtime
regressions. BLAKE3 also passed run 32 at `3d1bcb3`. These are shared-framework
results, not a complete WOTS pass. Both BLAKE3 and G1 passed run 33 at
`e959f9e`, including the SDK limit-diagnostic change. The new bounded timeout
diagnostics require another shared regression run.

Publication to the existing draft PR branch and hosted CI are authorized.
Merging, deployment and an external ranked submission are not authorized.
