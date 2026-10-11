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
| Finite query support and measurable oracle-program families | OracleSupport | `baf5657` |
| Exact UInt32 Fermat-prime reduction | MachineFieldReduction.reduceMachineField_toNat | `baf5657` |
| UInt32 Horner, residue-only coefficient reading and complete machine artifact/construction equality | MachineHorner, MachineCoinRead, MachineSharing (required by the selected diagnostic gate) | `d1648af` |
| Finite oracle law and VCV eager/lazy semantics bridge | FiniteOracleLaw, OracleMeasureBridge | `d1648af` |
| Distinct-label-pair marginal and guessing bounds | LabelGuessing | `d1648af` |
| Exact joint 32-byte coin-block law and allocated index injection | CoinBlocks, CoefficientIndices | `d0bd1ac` |
| Visible-coefficient privacy and exact query-domain separation/injectivity | VisibleCoefficientPrivacy, DomainSeparation, DomainInjectivity | `d0bd1ac` |
| Joint coefficient sampling bias and exact field-table law | JointSampler, FieldTableLaw | `fba813c` |
| Joint independent-pad masking and preserved visible observations | MaskLaw, MaskedViewLaw | `fba813c` |
| Executable oracle reification, bounded execution traces and query parsers | OraclePrograms, OracleTrace, QueryTargets | `fba813c` |
| Fresh-cell programming retaining the full oracle/cache jointly | FreshOracleProgramming | `fba813c` |
| Uniform flat allocated polynomial table reindexing | PolynomialTableLaw | `807c1cf` |
| Ciphertext-dependent coefficient/pad transport | AdaptiveMaskedView | `807c1cf` |
| Complete cached construction equality, including every prepared byte | CachedSharing.cachedConstruction_eq | `807c1cf` |
| Actual coefficient polynomial correspondence and chain tape | ActualPolynomialTable, ChainTape | `e806ba6` |
| Nonce independence and restricted oracle-program representation | NonceTableLaw, NonceEnvironmentLaw, RestrictedOracleProgram | `e806ba6` |
| Joint execution coupling, normalized good fibers and exact two-answer mask representation | JointOracleTrace, UniformGoodFiber, TwoHashMask | `05cd4d5` |
| Complete protected honest correctness and actual artifact-address injection | Expansion.construction_correct, ArtifactAddresses | `f0b2e08` |
| Common finite oracle domain, visible coefficient transport and sixteen-limb Horner projection | CommonOracleDomain, VisibleCoefficientTransport, LaneImplementation, LaneHorner | `f0b2e08` |
| Complete lane construction equality and finite trace/product transport | LaneSharing.laneConstruction_eq, MultiTargetTrace, GoodKernelSubstitution, CanonicalLabels, CiphertextConditionedPrivacy, ProductEventBounds | `e8e1f95` |
| Withholding reduction budget fits the protected numerical target | WithholdingBudget.withholding_bound_fits_target (arithmetic only) | `cd334f2` |
| Chain collision probability, ideal chain programming, and adaptive target arithmetic | ChainCollisionLaw, ChainProgrammingLaw, AdaptiveBudget | `cd24df3` |
| Public/hidden chain partition, message-visible signature partition, exact nonce and joint coefficient-sampling law | ChainPartitionLaw, MessagePartition, NonceCoefficientCoordinates | `a03a0ac` |
| Direct byte-fold reader, complete updated lane equality, and guessing from the full selected-label table | MachineCoinRead.directFieldLoop_eq, LaneSharing.laneConstruction_eq, JointLabelGuessing | `1e00f92` |
| Exact oracle overlay and inverse fibers | OracleOverlay | `0ab64e1` |

## Current validation attempt

Run 47 (`0ab64e1`) checked **89 of 120 modules**. Four modules had direct
errors (`HonestQueryBudget`, `UniformOverlay`, `SelectedLabelTrace`,
`FiniteChainLaw`); 27 dependents were blocked. `OracleOverlay` now passes.
Universal honest correctness and the complete direct-reader machine/cached/lane
equality remain checked. The complete withholding and adaptive security
reductions remain unchecked.

**The generated lane tools passed both the standard SDK integration and the
independent complete reference-artifact/later-message correspondence check.**
The SDK test suite took 65.51 seconds in total, with its existing 60-second
per-tool limit enforced. It observed the exact **48,752,768-byte artifact** and
8,192 released bytes. The independent correspondence test took 121.91 seconds;
three generated expansions took 10.014, 11.430 and 10.188 seconds. These are
completed runtime diagnostics, not a security certificate or accepted submission.

The executable build completed 6,193 jobs with compiler peak RSS
**3,421,212,672 bytes**. SDK native peak RSS was **833,302,528 bytes**;
independent correspondence peak RSS was **789,868,544 bytes**. The runtime
probe finished at 1,224.798 seconds. Successful source batches totaled
399.27 seconds across 27 invocations, excluding failed batches and retries.
All checks stayed within the unchanged memory, tool and author limits.
The separate Rust reference full-artifact/later-message test passed in
24.74 seconds with 320,360,448 bytes peak RSS.

The follow-up names the indexed lists explicitly, proves the product-event
set equalities, annotates the noncomputable oracle-derived tape, and avoids a
dependent subtype rewrite. The query-budget wrapper now uses the same abstract
two-program combinator as its bound theorem: diagnostics showed the previous
proof unfolded chain recursion over 271,000 times. This reification refactor
preserves the executable construction and oracle calls. These fixes still need
the pinned compiler. No statement, sampler, serialization, backend, resource
cap, or acceptance gate was changed. The certificate remains absent and the
score unranked.

An additional local source review found nine analogous product-event rewrites
in seven downstream modules. They now use explicit extensional set equalities
instead of treating conjunction with `True` as definitional equality. This
review checked the reduction's joint sampler loss, full oracle/ciphertext
coordinates, message/state coupling before message-specific partitioning,
and three separately accounted collision losses. No additional mathematical
gap was identified by that review; the bridge proofs and these local repairs
remain compiler-unchecked. Publication is paused pending approval, so this is
not evidence of a newer hosted pass.

The runtime probe now atomically retains its last completed phase and available
build/SDK measurements. The verifier prints that evidence even after an outer
timeout. Stale reports are cleared, incomplete phases do not count as passes,
and failure-injection tests cover build, SDK and correspondence failures. This
changes diagnostic retention only; the same proof gates, tests and limits apply.

To avoid repeated Lake graph startup, author checks batch ready dependency
layers within the same capped process and with one Lean thread. A successful
batch exit certifies all requested targets; an ordinary failure triggers
individual target checks. Resource failures stop without retries. Neither
logs nor existing olean files are used as evidence of compilation. The isolated
verifier and native proof gates are unchanged.

The optional diagnostic stays inside the **same single 1,800-second author
check**, with unchanged memory and per-tool limits. Source errors remain fatal;
resource failures stop immediately. The diagnostic cannot produce an accepted
submission. Failure-injection tests cover both the requested-proof gate and
the executable builder's independent proof gate. The certificate remains absent.

Completed run 35 at `d1648af` reached the **machine** runtime diagnostic,
whose selection requires successful compilation of `MachineSharing` and all
its dependencies. Thus the UInt32 Horner evaluator, residue-only coin decoder
and full machine construction equality were checked. The retained log also
explicitly records successful `LabelGuessing` and `OracleMeasureBridge` builds
(the latter includes `FiniteOracleLaw`). The cached-chain equality did not
pass. This is proof evidence, not a native performance measurement.

The combined author check exceeded its unchanged 1,800-second cap while
building the diagnostic executable. Its bounded timeout output retained only
the last 8 KB, losing the earlier direct source diagnostics. The run provides
no machine runtime or artifact-correspondence result. Run 34 had built the
original executable and established a `garble` timeout at 60.005 seconds,
with no side-output overflow. The cached candidate was selected following the checked equality in run 38; lane replaced it after run 42.

The follow-up persists each source result and prints that diagnostic record
even after an outer timeout. Failure-injection tests verify that diagnostics
cannot suppress rejection and that stale records are removed. When sources
fail, the default author preview now returns their errors without the optional
runtime probe. The probe remains available via `check_lean.py --runtime-probe`;
a complete source build still proceeds to the mandatory isolated verifier and
native tests. No acceptance or resource limit is relaxed.

Executable machine definitions have been moved unchanged to
`MachineImplementation`, separate from proof-only imports. Before building an
optimized executable, `check_runtime_probe.py` explicitly compiles its complete
equality module. The complete machine and cached equality modules passed after this import refactor. It does not replace
Lean code with a native implementation, alter the selected candidate or imply
a timing improvement.

The remaining security modules are proof attempts with explicit premises,
not assumptions admitted into a candidate certificate. They cover coefficient
sampling, actual oracle programs, query traces, domain separation, ideal chain
collisions/partitions/programming, and ciphertext-preserving adaptive views.
The actual joint real/ideal reduction remains unchecked. `FreshOracleProgramming`
attempts a fresh-cell joint law retaining the whole oracle and fixed cache;
`OracleOverlay` attempts joint key/oracle programming fiber counts. The fresh-cell law passed run 37; the overlay fibers remain unchecked,
and fiber counts alone are not normalized probability laws. Source declarations in blocked modules do not count as checked results.

## Obligations still open

| Obligation | Remaining work |
| --- | --- |
| Universal honest correctness | Checked in run 41; carry the theorem into the final certificate |
| Complete coefficient law | Check the byte-level plaintext specialization and integrate the checked joint nonce/field sampling law into actual games |
| Joint visible-share privacy | Check the full sampled coefficient-table specialization, including all 16 limbs and all 512 labels |
| Actual oracle programs | Complete measurable winning events and the honest query budget; executable reification is checked |
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
tests pass. They do not prove the candidate. Hosted run 34 measured Rust Prepare
at 18.07 seconds, the full fixed-artifact three-message test at 23.83 seconds,
and peak RSS at 320,389,120 bytes.
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
`e959f9e`, including the SDK limit-diagnostic change. BLAKE3 and G1 also passed runs 34 and 35, including the bounded timeout
diagnostics. These passes do not certify WOTS.

Publication to the existing draft PR branch and hosted CI are authorized.
Merging, deployment and an external ranked submission are not authorized.
