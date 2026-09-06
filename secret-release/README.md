# SecretRelease

The common contract is [one file](SecretRelease.lean). It contains no BLAKE3,
G1, half-gates, circuit compiler, SHA implementation, checksum theorem, or
construction-security reduction. The standalone `secretRelease` Lake package
pins VCVio and Mathlib on Lean 4.33.1; it has no dependency on either challenge.
The example declarations, audits, and native checks are outside the contract.

`SecretRelease.Examples.blake3` is a complete challenge declaration against
Clean's BLAKE3 reference. [`privateMap`](SecretRelease/Examples.lean) shows the declaration pattern for
`Q + [r]A`: valid affine inputs, private canonical `(Q,r)`, plaintext canonical
point output, and the current equal-leakage comparison. These are new declarations, not
certified solutions or replacements for the existing ranked contracts.
The BLAKE3 example additionally requires withholding every input/output label
before either disclosure channel arrives. The existing ranked BLAKE3 predicate
still specifies only its original post-release recovery experiment.

The separate [`g1-release` challenge](../g1-release/README.md) now instantiates
`Certified` for BN254 `Q + [r]A`, with proved canonical codecs, plaintext output,
post-release opposite-label recovery, and equal-result private-map privacy. Its
verifier builds and exports a certificate-gated native executable using a trusted
C SHA-256 runtime. Its checked-in entry is unranked; the old ideal-pad challenge
and BLAKE3 acceptance predicates remain separate.

## Use the shared package

From a sibling challenge's `lakefile.lean`:

```lean
require secretRelease from "../secret-release"
```

A challenge at the repository root uses `"secret-release"` instead. Each
consumer commits its resolved manifest with the same Lean/dependency pins.
The existing G1 package has not been migrated or given a new dependency.

```lean
import SecretRelease             -- one-file contract and ROM profile
import SecretRelease.Simulation  -- optional VCVio simulation/cost infrastructure
```

The second import exposes the pinned upstream definitions directly:

| VCVio definition | Purpose |
| --- | --- |
| `Interaction.UC.ObservedCompUCSecure` | Existential simulator and real/ideal distinguishing bound. |
| `Interaction.UC.ObservedCompEmulates` | Real/ideal comparison and composition bounds. |
| `Interaction.UC.AsympObservedCompEmulates` | Negligible advantage for an explicitly specified adversary class. |
| `OracleComp.Complexity.StrictPPTWitness` | Uniform program realization and polynomial resource bounds relative to a quantitative backend. |
| `OracleComp.Complexity.PureCertificate` | Cost certificate for local computation, including computations that make no oracle queries. |
| `SecurityGame.ReductionWithCost` | Reduction with a monotone resource-bound transformation. |

**Importing these definitions does not add simulation security to `Certified`.**
The author must define the ideal functionality, allowed leakage, schedule and
execution semantics, fix a meaningful adversary class and quantitative backend,
and require the construction's real/ideal proof and simulator efficiency proof.
The fixed-advantage UC definition itself does not impose PPT. The PPT witnesses
are backend-relative; treating them as ordinary machine-time bounds requires
an adequate backend interpretation. Counting only oracle calls does not bound
an arbitrary pure discrete-log search.

For plaintext `[r]A`, a useful ideal interface gives the simulator `A` and `T=[r]A`
and withholds `r`. A simulator cannot be allowed to recover `r` by exhaustive
search for free. An efficient simulation theorem establishes no additional
leakage; computational secrecy of `r` from `(A,T)` additionally needs a reviewed
group-hardness assumption. Neither claim is asserted by this package today.
The ROM-to-SHA-256 implementation bridge also remains heuristic.

Generic declaration patterns live in `SecretRelease/Examples.lean`; tests live
in `SecretReleaseTests/`. Construction proofs are deliberately outside the common contract.
The BLAKE3 verifier copies this package's protected source into a fresh sibling
directory, discards its local build/config caches, and builds and audits both
imports under the existing caps. The disk quota covers both sibling packages.
External dependencies still require exact Git
pins and authenticated caches. The immutable-base submission overlay protects
the whole shared directory; changing its source and the digest is not admissible
as a contestant submission. Authoring previews remain unranked.

## Declare a challenge

```lean
import SecretRelease

-- Supply the reference, codecs, and reviewed ROM bound in this file.
def challenge : SecretRelease.Challenge where
  Private := PrivateInput
  Input := InputValue
  Output := OutputValue
  privateCodec := privateCodec
  inputCodec := inputCodec
  inputs := SecretRelease.Lamport inputCodec
  outputs := SecretRelease.Lamport outputCodec
  reference := reference
  Claim := ForbiddenDisclosure
  wins := forbiddenDisclosure
  rom := reviewedBound
```

This snippet is a template; see the compiling
[BLAKE3 declaration](../blake3/SecretReleaseExamples.lean).

The author freezes this declaration before contestants submit anything.
`wins` is the reviewed definition of a forbidden disclosure, not an assumption
the contestant can supply. For signature-like inputs it checks a credential
for a different **valid** encoding. For BLAKE3 it checks recovery of any one
opposite input/output label. Those are different security properties.
`withholding := some beforeReleaseWins` optionally adds a separate pre-release
target, using the same claim type and ROM bounds. Its attacker sees only the
known input and artifact. `none` makes no pre-release promise.

`Codec.checked n valid` makes accepted bit strings a subtype, including any
checksum, canonical representation, or curve-membership condition. Correctness
covers valid typed values. The adversary's intermediate calculations remain
unrestricted; invalid data that eventually enables a forbidden valid disclosure
still wins. Merely calling an encoding valid does not prevent another valid
encoding from being freely derivable. That is an obligation for the chosen
encoding and security proof, not an extra universal restriction on codecs.
Before accepting a challenge declaration, check what an attacker can derive
from its disclosure channels while ignoring the artifact entirely. For example,
unrestricted ones-only encodings permit subset disclosures. No construction
can repair a forbidden claim already achievable through those fixed channels.

## Input/output mechanisms

| Definition | Private material and disclosure |
| --- | --- |
| `Lamport codec` | Uniform distinct 32-byte pairs, independently per bit; disclose the selected label at every bit. |
| `HORS n select` | Independent uniform 32-byte secrets; disclose the selected subset in increasing index order. |
| `OnesOnly codec` | `HORS` with the 1 positions of the encoded value as its selector. |
| `Preimage condition` | One uniform secret, disclosed when the condition is true. |
| `Plain encode` | No secret material; disclose the encoded value. |

These are disclosure mechanisms, not full signature suites. A public verification
key is not an implicit free channel. A future Winternitz mechanism can use a
custom `Disclosure`: uniform independent chain roots, oracle-derived chain nodes,
and a reviewed checksum/verification rule. Derived nodes need not be independent.
If verification accepts alternative preimages, the winning rule must use that
verification predicate; equality with the originally issued secret is weaker.

A `Disclosure` can choose any finite nonempty key space. Its uniform distribution
can therefore express admissibility constraints such as distinct label pairs.
The two key spaces, construction coins, and oracle are mutually independent.
Only these external spaces are fixed: internal wire labels may be correlated,
so free-XOR and half-gates are eligible.

## What a certificate means

`Certified challenge` contains the exact scheme and its claimed byte bound:

- Correctness through the actual encode/decode/evaluate path.
- Both artifact-codec round trips and a worst-case serialized byte bound.
- Post-release resistance to the challenge's forbidden claim in a shared ROM.
- If `withholding` is supplied, the additional pre-release target bound.
- If `privateLeakage` is supplied, indistinguishability for any two private
  inputs producing the same explicitly permitted leakage bytes.

`privateLeakage := some (fun p x => ...)` is a reviewed author choice, never
inferred from the full typed reference result. Constant empty leakage compares
all private inputs; `none` requests no private-parameter privacy. The G1 helper
explicitly permits the plaintext output bytes and requires an injective encoder.
This is privacy modulo deterministic leakage, **not** automatic simulation
relative to randomized disclosure channels. Selecting overly revealing leakage
weakens the goal; the author must justify it before freezing the challenge.

Exact correctness for all admissible keys, coins, and hash interpretations is
the default. The author may instead select `Correctness.statistical`, with a
nontrivial rational error bound over the experiment. That permits explicitly
bounded failure; it does not permit a contestant to weaken exact correctness.

The ROM profile fixes a query cap and an explicit rational error function below
one throughout that range. Rationals keep the challenge metadata executable;
probability measures remain proof-only. The example bound is `(q+1)/2^128`
through `q = 2^64`, matching the current BLAKE3 target numerically. A certificate
must establish it; choosing the profile supplies no security theorem.
Specifically, the allowed success probability is `2^-128` at zero queries and
`2^-64 + 2^-128` at the maximum query budget, approximately `2^-64`.

The evaluator knows the input. This initial profile is classical, one-shot,
and static-input. The post-release experiment gives the attacker both disclosure
channels for free, so it cannot establish withholding on its own. The optional
pre-release experiment supplies neither channel. These are separate marginal
experiments, not a multi-stage adaptive game. The profile does not cover
adaptive input selection, multiple releases, quantum queries,
timing leakage, or security of SHA-256 as an ideal oracle. Bounds hold for every
deterministic bounded-query attacker, including every fixed choice of auxiliary
coins; a randomized-attacker lifting theorem is not included here.

The examples' whole-label recovery goals do not promise that every bit of an
unreleased label stays confidential. Partial leakage can be consistent with
their guessing bound. General confidentiality needs an additional reviewed
indistinguishability or simulation definition. Distinct pairs exclude equality
within each pair; collisions across coordinates remain possible and must be
accounted for in construction proofs.

`maxBytes` is a proven score. An author wanting a hard cap can require
`SizeAccepted challenge limit`, where the trusted author/runner fixes `limit`.
That adds the proof `certified.maxBytes ≤ limit`; a submitted score by itself
does not enforce a threshold.

All public instance-dependent state must be serialized into the scored artifact.
Fixed compiled program code and the declared disclosure channels are outside
that score; specializing a binary with instance data is not a permitted escape.
Fixed codecs allow a future generic runtime to reject malformed private/input
encodings. The executable methods must compile even though their proof fields
may use noncomputable mathematics.

## Acceptance and runtime boundary

`Certified` is a mathematical certificate, not the complete executable
acceptance process. A challenge migration must bind it to all of these checks:

- An immutable base-owned challenge, verifier, and optional size threshold;
  `protected.sha256` checks consistency and is not itself a trust anchor.
- The committed Lean toolchain and dependency revisions, authenticated build
  products, and the exact certificate's axiom closure. Only `propext`,
  `Classical.choice`, and `Quot.sound` are allowed by the current checker.
- The existing submission source policy: no implementation replacement,
  compiler attributes, custom metaprogramming/recursion preprocessing, native
  proof evaluation, unsafe code, submission FFI, or file inclusion. Compilation
  alone does not establish agreement with the definitions used in proofs.
- The compiled certificate's exact algorithms, a protected byte parser connected
  to `inputCodec.decode`, and invalid-encoding rejection. The shared contract's
  evaluator currently takes a typed input; generic byte parsing is still pending.
- The existing sequential RAM/time/process/disk caps. Honest `garble`, `evaluate`,
  and `reveal` take a mathematical `Hash`; this certificate imposes no honest
  oracle-query or local-computation bound. Attacker queries remain explicitly
  bounded through `Program` and never receive that function for free.

The current BLAKE3 verifier enforces its existing source/build/runtime policy
and builds/audits the shared examples. It does not yet accept `SecretRelease`
certificates or provide their generic binary packager. The corresponding
migration and C-backend trust boundary remain the work below.

## Small implementation plan and feasibility

1. **Done here:** one-file contract, executable BLAKE3 declaration and G1
   declaration pattern, probability normalization and nonvacuity audits, disclosure
   and validity native tests, immutable-base CI integration.
2. **BLAKE3 migration:** adapt the existing byte runner and audit to the new
   declaration; explicitly verify equivalence of bit order, distinct-pair
   sampling, selected output, and the recovery game before changing acceptance.
   The new pre-release goal also needs a separate theorem; it is not equivalent
   to the old post-release certificate.
   This is manageable plumbing. Certifying its half-gates baseline still needs
   complete lowering/transport correctness and its correlated-label ROM proof.
3. **G1 challenge declared:** `g1-release` supplies the codecs/reference, preserves
   function privacy, and checks complete shared certificates. Certifying a
   construction remains open.
   The example also requires opposite-input-label recovery security, which the
   old `FunctionPrivate` predicate does not separately assert. Existing G1
   correctness/ideal-law proofs remain useful, but do not directly certify
   finite-key expansion through the public ROM. Keep its 5,940,480-byte result
   under its existing rules until that additional argument is established.
4. **Generic executable packaging:** `g1-release` already builds its own
   certificate-gated binary. A protected generic CLI for all challenges should execute a
   certificate's exact scheme, link the chosen pinned C SHA-256 backend, and
   publish the binary plus contract/source/dependency hashes and proof profile.
   The new `secret-release-checks` executable tests compilation; it is not a
   certified garbler or the finished packaging command. C/FFI/compiler trust
   and the heuristic ROM-to-SHA bridge must remain explicit.

No gate model restricts the solution space. The main intentional restrictions
are the classical ROM, one release, known static input, finite uniformly sampled
external keys, fixed input/private codecs, and worst-case artifact size. A future
reviewed PRF-based profile could reuse the same scheme/disclosure interface.

Keeping ideal private pad/modulus oracles as explicit primitives would make G1's
existing proof much easier to reuse, but would leave the finite-seed bridge
unproved. Treating a submission's own privacy statement as an assumption would
make certification vacuous and is not an acceptable shortcut. Trusting the C
hash implementation avoids a machine-code proof; it does not solve garbling
security or make SHA-256 an ideal random oracle.

All builds and tests retain the sequential 4 GiB build / 1 GiB native RSS caps.
