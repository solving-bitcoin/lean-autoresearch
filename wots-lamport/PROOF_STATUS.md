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

## Current validation attempt

Run 40 (`05cd4d5`) checked **68 of 81 modules**. Four modules had direct
errors (`MultiTargetTrace`, `CommonOracleDomain`, `Expansion`,
`HonestQueryBudget`), and nine dependents were blocked. Newly accepted modules
were `JointOracleTrace`, `UniformGoodFiber` and `TwoHashMask`. The final wrapper
correctness theorem still failed during type normalization; the universal
expansion theorem is not claimed as an accepted module. The reference job
passed.

The cached executable **built successfully**, after its complete equality
proof compiled, and reached the standard SDK integration test. `garble`
**timed out at 60.000052718 seconds**, with zero stdout/stderr side output.
The test process reported 64.41 seconds including its other checks. Full
artifact correspondence and later-message native tests did not run. The
selected cached implementation therefore fails the current runtime requirement.

The next batch introduces sixteen simultaneous scalar Horner accumulators and
transposes coefficient storage across limbs. `LaneHorner` and `LaneSharing`
attempt the complete correspondence, including every artifact byte. These
proofs and the performance improvement are **unchecked**. The diagnostic asks
for `lane` explicitly and runs it only after `LaneSharing` compiles; a rejected
lane proof does not remeasure the known-slow cached implementation. The actual
submission remains cached until the new equality is checked.

Other repairs address a generated finite-set induction instance, opaque
mathematical enumeration, semireducible wrapper types, and explicit query
continuations. New security proof attempts connect actual serialized mask and
commitment addresses, joint key/oracle programming, exact ciphertext body
serialization, full 64-byte pad randomness, visible field plaintext transport,
selected-label-dependent query lists, and independent pre-release coordinates.
They include no assumed candidate security theorem and remain unchecked.
The final withholding, post-release and adaptive reductions remain open.

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
with no side-output overflow. The cached candidate is selected following the checked equality in run 38.

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
The actual joint real/ideal reduction remains open. `FreshOracleProgramming`
attempts a fresh-cell joint law retaining the whole oracle and fixed cache;
`OracleOverlay` attempts joint key/oracle programming fiber counts. The fresh-cell law passed run 37; the overlay fibers remain unchecked,
and fiber counts alone are not normalized probability laws. Source declarations in blocked modules do not count as checked results.

## Obligations still open

| Obligation | Remaining work |
| --- | --- |
| Universal honest correctness | Check Expansion through `construction_correct` for the exact protected wrapper |
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
