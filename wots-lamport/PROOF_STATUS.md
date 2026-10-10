# Proof and validation status

Hosted Lean at a2dce49 checked all Protected modules through Wire, including
encoding round trips, chain/signature laws and the public-key wrapper. The next
benchmark failed its frozen digest after setup; full candidate proofs and
generated tools remain unchecked.
The pinned compiler is 4.33.1. Local installation returned proxy 403; GitHub
Actions successfully installed it through the authorized hosted workflow.
That denial was not bypassed. The project contains no `sorry`, new axioms or
fake certificate. Source-level theorem bodies are **unchecked proof attempts**.

| Obligation | Current deliverable | Remaining work |
| --- | --- | --- |
| Full 256-bit message coverage | Encoding/decoding, `decode_encode`, canonical extraction | Compile and repair/check actual proofs |
| Canonical Sign accepted | Correlated seeds/chain recurrence, `sign_verifies` | Kernel-check proof; actual Script correspondence |
| Same artifact, all messages | Lean and independent Rust weighted-sharing algorithms | Prove `Correct` universally for every hash, coins, key and distinct label table |
| Bit order | Explicit high/low nibble to LSB-first formula; exhaustive finite Python/Rust fixtures | Formal mapping theorem |
| Weighted geometry | Checksum identity, multiplicity/telescoping lemmas; all 961 totals tested | Connect full slot enumeration to exact count for every message/wire |
| Field reconstruction | Executable F_65537 interpolation, duplicate/nonzero checks, reference tests | Field primality/coordinate lemmas and Lagrange reconstruction theorem |
| Shamir privacy | Toy F_7 exhaustive distribution test only | Check abstract reconstruction and secret-shift bijection in Shamir.lean; connect all 16 limbs and all polynomials to sampled distributions |
| Coefficient law | Independent 32-byte blocks; explicit bias formula | Prove modular-sampling statistical distance and compose across coefficients |
| Chain/mask ROM reduction | Real correlated disclosure; full-closure adversary tests | Joint bad-query/collision coupling including setup, endpoints, masks, commitments and label-recovery guessing |
| Public pk visible | Mandatory protected wrapper, `publicKey_visible`, audited Entry mapping | Compile and audit theorem and generated serialization |
| Pre-release withholding | Nonvacuous author-owned game recovering either label | Prove `ROM.WithholdingSecure` |
| Post-release opposite label | Nonvacuous author-owned static game, outputs free | Prove `ROM.ReleaseSecure` against all bounded-query programs |
| Exact artifact codec | Raw bytes, identity encode and `some` decode | Supply shared certificate codec fields; malformed body checks are distinct |
| Universal byte bound | Fixed layout/loop sizes; claimed 48,752,768 bytes | Prove `ArtifactBound`, including prefix and every table for all inputs |
| Actual executable correspondence | Rust reference and generated SRTools integration test added | Compile generated Lean tools and run independent end-to-end tests within all caps |
| Adaptive input | Protected artifact-first two-stage game | Prove separate adaptive bound; no implication from static game |
| Simulation/GC composition | Boundary documented | Formal ideal interface, simulation and joint labels theorem not implemented |
| Every raw Script witness | Types distinguish canonical, semantic, raw witnesses | Fix full interpreter/flags normalization and prove relation; canonical adapter rejects aliases |
| Malicious setup/fraud protocol | Boundary documented; mismatched-instance regression tests | Authenticated GC/transaction/label binding, availability and Bitcoin-verifiable evidence design |

## Numerical target is not a proved reduction

The protected target uses 256-bit independent seeds, q<=2^48,
an honest-query budget 2^32 and multi-target multiplier 2^20. These are fixed
challenge parameters. Merely proving the rational expression is below one
does not prove a candidate's security. The ledger must include:

- 67 chains (989 chain steps to compute all endpoints), possible collisions
  within/across chains and with derived oracle inputs;
- every setup/evaluation mask query, including repeats and public endpoints;
- 512 public label commitments and 512 label-recovery targets;
- all 1,015,296 encrypted evaluations, with two mask blocks each;
- coefficient sampling bias, correlations induced by the shared oracle and
  unrestricted local adversarial computation;
- the difference between the independent seed model and upstream's derivation;
- separate pre-release, static post-release and adaptive experiments.

The supplied fixed-sum T=0 singleton is excluded by this track's T=1023.
The optional enumerative 66-digit laboratory is not implemented; it was not
substituted for the direct 67-chain target.

## Environment baseline

Rust 1.97.1 was installed from the official installer within `/workspace`.
The original repository's policy, overlay and resource configuration tests
passed. Its verifier regression suite fails when killed descendants become
unreaped zombies under PID 1 (`tail -f /dev/null`). Running the unchanged suite
under a temporary child-reaping supervisor passes. No repository guard was
weakened or patched to hide this environment dependency. A suitable process
supervisor is still required for the normal full verifier in this container.

## Status gate

`Submission.submission.certificate = none`; `score.txt = unranked`.
The certificate fields are deliberately not filled with assumptions. Before
claiming a complete implementation, discharge the universal functional and
security obligations above, compile all Lean sources, run the actual generated
tools and review the new protected boundary. Publication of a feature branch
and draft PR to solving-bitcoin/lean-autoresearch is authorized. Merging and
external ranked submission are not authorized.
