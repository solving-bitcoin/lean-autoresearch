# Proof and validation status

**All 120 source modules and the certificate assembly compiled in run 69;
final isolated acceptance is pending.** The pinned compiler is Lean 4.33.1.
The complete correctness, withholding, static post-release and artifact-first
adaptive security proofs apply to the protected ROM model. The candidate has
a proof-bearing certificate and `score.txt = 48752768`. Its isolated namespace
audit rejected a lazily generated shared byte-codec equation; the current repair
is not yet checked. No accepted or externally ranked submission is claimed.
Rust/Python tests are independent validation, not Lean proofs.

## Compiler-checked results

The following modules passed hosted Lean elaboration. All imported submission
sources and certificate assembly passed run 69. Final isolated acceptance remains
a separate check.

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
| Joint uniform overlay law, selected-label trace guessing, and finite chain programming law | UniformOverlay, SelectedLabelTrace, FiniteChainLaw | `e533a8f` |
| Actual mask and commitment programming reads and chain consistency | ArtifactProgramming | `3915686` |
| Selected-label trace coupling, finite artifact/chain joint programming, and full answer coordinates | SelectedTraceCoupling, FiniteArtifactLaw, IdealArtifact, CombinedProgrammingLaw, ArtifactAnswerCoordinates | `fd186f4` |
| Concrete pre-release query trace bound, field plaintext, ciphertext serialization and finite programming bridge | ProgrammedQueryTrace, FieldPlaintext, CiphertextArtifact, FiniteProgrammingBridge | `2b799bd` |
| Pre-release canonical label and nonce/coefficient coordinates | BeforeReleaseCoordinates | `ad5f54f` |
| Restricted programmed oracle agrees away from hidden targets | VisibleProgrammedOracle | `642de89` |
| Complete honest query budget, transported field artifact coordinates and visible tape congruence | HonestQueryBudget, FieldArtifactCoordinates, VisibleTapeOracle | `71c3c5f` |
| Canonical visible oracle after coefficient transport | CanonicalVisibleOracle | `346336e` |
| Reified game execution/query bounds and conditional post-release trace/guessing bound | GamePrograms, AfterReleaseCoordinates | `1b590f8` |
| Fixed-message and withholding game reductions | GameReductions | `620a1a4` |
| Protected infinite-oracle game equals one joint finite-table law | GroupedOracleLaw | `d94b293` |
| Conditional post-release joint trace and guessing law | AfterReleaseLaw | `3fe2c26` |
| Complete protected withholding security and raw post-release joint bound | PreReleaseFiniteGame.construction_withholdingSecure, RawAfterReleaseLaw | `4577cd3` |
| Adaptive uniform-field probability bound with whole message/state coupling | AdaptiveFieldGame | `a2dd73f` |
| Actual packed-coin adaptive bound with one joint sampler loss | AdaptiveCoinLaw | `b7acbfa` |
| Exact adaptive programmed-game, ciphertext and actual-coin event correspondence | AdaptiveProgrammingBridge | `b03588e` |
| Complete protected adaptive and static post-release ROM security, all imported source modules | AdaptiveFiniteGame.construction_adaptiveSecure, construction_releaseSecure, Solution | `f8597c9` |
| Exact lane certificate assembly and separate adaptive theorem | Solution.constructionCertificate, laneCertificate, lane_adaptiveSecure | `6bd0042` |

## Current validation attempt

Run 69 (`7d33a2c`) checked **120 of 120 modules**, including certificate
assembly and the separate `lane_adaptiveSecure` theorem. There were no failed
or blocked source modules. Source batches took 727.903 seconds across 38
batches with 4,367,511,552 bytes peak RSS.

The isolated verifier built protected imports/shared checks, passed protected
boundary/axiom audits, negative certificate/packed-proof checks and fixture
native/SDK tests. It built the candidate, then rejected the namespace audit:
`submission declares outside its namespace: SecretRelease.Codec.byteVector.eq_1`.
The prior protected output-codec/bit/weight unfolding repairs compiled. The
current repair replaces the remaining shared byte-codec unfold in
`LabelBridge.byteVector_encode_raw` with its explicit bit-vector expression.
Protected definitions and audit checks remain unchanged. Final candidate native
tests and bundle acceptance did not run; no run-69 correspondence pass is claimed.

The separate run-69 Rust reference test passed in 38.12 seconds with
320,237,568 bytes peak RSS. BLAKE3 passed run 69; the unchanged G1 repeat was
still active at publication and may be superseded. Both passed run 65.

**Run 66 passed generated SDK integration and full independent reference
correspondence**, observing the exact **48,752,768-byte artifact** and 8,192
released bytes. The SDK suite took 53.05 seconds and independent correspondence
97.04 seconds; generated expansions took 8.074305455 / 9.384781171 /
9.078928507 seconds. Compiler, SDK-native and independent-native peak RSS were
3,421,310,976 / 883,707,904 / 854,679,552 bytes. The runtime probe completed in
920.097 seconds inside the unchanged 1,800-second author cap. Full validation
did not pass in run 66 because of its then-remaining source error. The separate Rust reference test
passed in 23.36 seconds with 320,413,696 bytes peak RSS. Both shared previews
passed run 65; their unchanged run-66 repeats were still active at publication.

Run 57 also passed generated SDK integration and independent correspondence.
Runs 58 through 65 reached the unchanged author cap during executable building.
A completed runtime diagnostic does not certify the security proofs.

Run 56 reached the author cap during executable building; run 55 completed
compilation but reached the cap during SDK checking. Run 52 completed SDK and
independent correspondence in 53.93 and 99.49 seconds. All limits are unchanged;
a completed runtime diagnostic does not certify the security proofs.

Run 51 passed SDK integration but reached the unchanged 1,800-second author
cap during independent correspondence. Run 50 completed both tests. A started
phase is never treated as a completed test.

Run 47 (`0ab64e1`) remains the first completed generated-tool correspondence
milestone: SDK suite 65.51 seconds, independent correspondence 121.91 seconds,
expansions 10.013809353 / 11.430133555 / 10.188375942 seconds. Its compiler,
SDK-native and independent-native peaks were 3,421,212,672 / 833,302,528 /
789,868,544 bytes respectively.

The current candidate assembles the checked correctness, codec, size and
security theorems, transfers them through `laneConstruction_eq`, and exposes
`lane_adaptiveSecure`. The private-leakage field is vacuous for this Unit/none
profile; it is not a GC simulation claim. Certificate assembly compiled in run 69; the remaining shared byte-codec
unfolding repair requires a new compiler/audit run. No security statement,
sampler, executable construction, resource cap or acceptance gate was weakened.

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
the executable builder's independent proof gate. A diagnostic cannot certify an entry.

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

The joint coefficient/nonce law, full oracle/ciphertext coordinates,
message/state coupling before message-specific partitioning, three collision
losses, withholding and complete adaptive/static ROM reductions all passed
source compilation. Their axioms must still pass the final candidate audit.

## Obligations still open

| Obligation | Remaining work |
| --- | --- |
| Namespace and axiom closure | Validate the remaining shared byte-codec unfolding repair with the unchanged isolated candidate audit |
| Final certified bundle | Run candidate native/SDK tests and binary/kernel/score consistency checks |

The mathematical ROM obligations are checked. Concrete SHA-256 security,
upstream master-seed equivalence, arbitrary raw Script witnesses, malicious
setup and GC simulation remain separate unclaimed results.

## Fixed numerical target

The author-owned target is `2^20 * (q + 2^32 + 1)^2 / 2^256`, for
`q <= 2^48`. Its nontriviality and the complete ROM reductions are checked.
The accounting covers 67 correlated chains (989 endpoint steps), 512 label
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
implied by the checked ROM reductions or the candidate certificate.
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
