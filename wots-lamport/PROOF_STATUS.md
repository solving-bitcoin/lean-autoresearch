# Proof and validation status

Hosted Lean checked all Protected modules through Wire at `a2dce49`, including
encoding round trips, chain/signature laws and the public-key wrapper. At
`50e6007` it also checked the shared `Runtime.garblePacked_eq` theorem: the
optional packed-byte implementation equals the mathematical vector operation
for every valid coin vector. At `18aebd8`, Threshold, Adaptive, Contract and
RunnerFixture compiled. That run exposed candidate elaboration failures;
at `f605fb5`, Sharing, Shamir and FieldBridge compiled. This checks abstract
Lagrange reconstruction, the Shamir secret-shift bijection, distinct nonzero
coordinates, and the modular Horner/field evaluation bridge. Layout and one
Nonvacuity theorem failed and are being repaired. The added canonical-integer
Horner corollary still needs compilation. Generated executable tools have not
yet been validated. The `da8f424` all-source attempt exceeded the unchanged
8 GiB aggregate build guard (8,645,795,840-byte peak); the next attempt uses
sequential module builds and kernel-only reduction of the finite slot geometry.
The `6d26fba` run confirmed that full slot enumeration alone still exceeds
the cap (8,897,998,848-byte peak). The next proof uses symbolic per-chain sums
and reduces only eight nibble cases. No native evaluation axiom or larger
memory budget is used. BitMapping and the canonical Horner corollary also
received elaboration repairs; InverseBridge is a new, unchecked proof attempt
for the executable inversion loop and bounded natural subtraction. At
`d048390`, all Nonvacuity theorems and the canonical Horner integer-result
corollary compiled. Two elaboration errors remained (target-digit case
selection and reduction of the modulus to zero); their dependent geometry
and size modules therefore did not build. At `d67ce75`, BitMapping and
InverseBridge compiled in full. Geometry failed on a simplifier mismatch
between a Fin cast and its natural value; the repaired hypothesis uses the
natural value explicitly. Layout remains blocked on that dependency.
The `8857322` attempt stopped before Lean because the new author-owned cost
fixtures were not included in the frozen digest. The digest is refreshed with
those files; admission rules are unchanged. `Exposed` now attempts to connect
filtered executable slots to the exact selected/opposite threshold counts;
it has not yet been checked by Lean.
At `80d2a99`, Geometry compiled, proving the weighted codeword sum 960 and
remaining depth 1023. Layout reached ordinary elaboration errors (a Boolean
conditional, sum scope and the concrete Lamport key type), without a resource
rejection. Those are repaired for the next run. New unchecked work adds the
polynomial degree/constant-coefficient bridge and a full limbwise connection
from the executable interpolation loops to Lagrange interpolation. Its small
factor/weight helpers preserve the previous executable algorithm.
At `6f344d2`, FieldBridge compiled with the new degree and constant-term
lemmas. InterpolationBridge needs explicit Nat-to-field coercions and reduced
tuple projections; Layout needs explicit partial-function unfolding and a
concrete, definitionally equal Lamport key type in `prepare`. The next batch
also attempts exact integer reconstruction, byte-mask cancellation, field
serialization round trips and extraction/decryption of every table row.
These new ByteBridge and reconstruction results are not yet compiler-checked.
At `e65c736`, Layout and Exposed compiled: the full universal artifact bound
is 48,752,768 bytes, and selected/opposite visible slot counts equal the
threshold/threshold-minus-one for every message and wire. InterpolationBridge
reached only a final function-composition simplification error; ByteBridge
reported four ordinary proof errors. The next batch repairs these and adds
explicit filtered-coordinate uniqueness, prepared-body slice identities and
honest share decoding/reconstruction. These additions and the expansion
refactor remain unchecked until the next hosted run.
At `6531e8e`, Sharing compiled after the expansion refactor, and the complete
InterpolationBridge compiled, including exact natural-number reconstruction.
ByteBridge now has one remaining field-byte round-trip error; new indexed-slot
lemmas have three elaboration errors. The next batch repairs these and attempts
the full `Correct (wrapped construction)` theorem through prepared slices,
label repacking and commitment checking. It also adds uniform polynomial-law
transport (including finite families), the actual opposite-coordinate privacy
specialization, and an exact symbolic residue-fiber count for a uniform
256-bit integer. All these new results remain unchecked. The sampler theorem
does not yet connect coin-byte blocks or compose distance bounds, and no joint
ROM reduction or security certificate is claimed.
At `00cc333`, ByteBridge, the complete indexed-slot Exposed module, ShamirLaw
and VisiblePrivacy compiled. This checks exact share-byte decoding primitives,
uniform-law transport for finite polynomial families, and the actual opposite
coordinate set's uniform-polynomial privacy statement. ArtifactBridge still
needs slice arithmetic/finite-index repairs; LabelBridge has one symbolic
multiplication-order proof error, and SamplerLaw needs a tuple projection and
non-looping cardinality simplification. New unchecked CoinEncoding/CoinBlocks
and CoefficientIndices work connects uniform coin bytes, independent blocks and
the actual polynomial coefficient addresses. SamplerMixture attempts an exact
mixture law and two-sided marginal event bounds. Neither the complete expansion
proof nor a joint ROM security theorem is yet established.

At `c855881`, the remaining ArtifactBridge diagnostics are two Boolean-slice
arithmetic goals; SamplerLaw has one set/subtype cardinality rewrite mismatch.
The next batch repairs those and adds joint product-measure domination,
two-sided coefficient-table event bounds, exact byte-to-field pushforward laws,
and the coefficient-vector/bounded-polynomial equivalence. These additions
are unverified until hosted Lean succeeds. Full correctness and the joint
ROM reduction remain open; no certificate is issued.

The independent pinned Script comparison is now locally reproduced in
`BITCOIN_COST.md`: maximum complete-spend sizes are 2,101 vbytes for the
exact SHA-256/FullWidth WOTS profile and 7,209 for 256-bit SHA-256 Lamport.
This does not discharge the Lean or ROM obligations. Core download was
denied by proxy 403; no Core consensus/policy acceptance is claimed.

The pinned compiler is 4.33.1. Local installation returned proxy 403; GitHub
Actions successfully installed it through the authorized hosted workflow.
That denial was not bypassed. The project contains no `sorry`, new axioms or
fake certificate. Proof source is not counted as a proved result until the
pinned compiler checks it. The status below distinguishes checked modules
from remaining proof obligations.

| Obligation | Current deliverable | Remaining work |
| --- | --- | --- |
| Full 256-bit message coverage | Encoding/decoding, `decode_encode`, canonical extraction | Checked in Protected.Encoding |
| Canonical Sign accepted | Correlated seeds/chain recurrence, `sign_verifies` | Canonical theorem checked; actual Script correspondence remains open |
| Same artifact, all messages | Lean and independent Rust weighted-sharing algorithms | Prove `Correct` universally for every hash, coins, key and distinct label table |
| Bit order | General `BitMapping` theorem checked; exhaustive finite Python/Rust fixtures | Connect to complete expansion correctness |
| Weighted geometry | Geometry and exact selected/opposite filtered-slot counts checked | Check explicit coordinate enumeration and connect decoding |
| Field reconstruction | Executable F_65537 interpolation through exact integer reconstruction checked | Connect actual body decoding and label repacking |
| Shamir privacy | Abstract secret-shift bijection checked; toy F_7 exhaustive test | Connect all 16 limbs and all polynomials to sampled distributions |
| Coefficient law | Independent 32-byte blocks; explicit bias formula | Prove modular-sampling statistical distance and compose across coefficients |
| Chain/mask ROM reduction | Real correlated disclosure; full-closure adversary tests | Joint bad-query/collision coupling including setup, endpoints, masks, commitments and label-recovery guessing |
| Public pk visible | Mandatory protected wrapper, `publicKey_visible`, audited Entry mapping | Wrapper theorem checked; audit generated serialization |
| Pre-release withholding | Nonvacuous author-owned game recovering either label | Prove `ROM.WithholdingSecure` |
| Post-release opposite label | Nonvacuous author-owned static game, outputs free | Prove `ROM.ReleaseSecure` against all bounded-query programs |
| Exact artifact codec | Raw bytes, identity encode and `some` decode | Supply shared certificate codec fields; malformed body checks are distinct |
| Universal byte bound | Universal `Layout.artifact_bound` checked for 48,752,768 bytes | Validate generated executable bytes |
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
