# SecretRelease

The common contract is [one file](SecretRelease.lean). It contains no BLAKE3,
G1, half-gates, circuit compiler, SHA implementation, checksum theorem, or
construction-security reduction. It uses the existing pinned VCVio/Mathlib
dependencies. The example declarations, audits, and native checks are outside
the contract.

`SecretReleaseExamples.blake3` is a complete challenge declaration against
Clean's BLAKE3 reference. `privateMap` shows the declaration pattern for
`Q + [r]A`: valid affine inputs, private canonical `(Q,r)`, plaintext canonical
point output, and hidden-parameter privacy. These are new declarations, not
certified solutions or replacements for the existing ranked contracts.

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

This snippet is a template; the small compiling BLAKE3 declaration is in
[SecretReleaseExamples.lean](SecretReleaseExamples.lean).

The author freezes this declaration before contestants submit anything.
`wins` is the reviewed definition of a forbidden disclosure, not an assumption
the contestant can supply. For signature-like inputs it checks a credential
for a different **valid** encoding. For BLAKE3 it checks recovery of any one
opposite input/output label. Those are different security properties.

`Codec.checked n valid` makes accepted bit strings a subtype, including any
checksum, canonical representation, or curve-membership condition. Correctness
covers valid typed values. The adversary's intermediate calculations remain
unrestricted; invalid data that eventually enables a forbidden valid disclosure
still wins. Merely calling an encoding valid does not prevent another valid
encoding from being freely derivable. That is an obligation for the chosen
encoding and security proof, not an extra universal restriction on codecs.

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

A `Disclosure` can choose any finite nonempty key space. Its uniform distribution
can therefore express admissibility constraints such as distinct label pairs.
The two key spaces, construction coins, and oracle are mutually independent.
Only these external spaces are fixed: internal wire labels may be correlated,
so free-XOR and half-gates are eligible.

## What a certificate means

`Certified challenge` contains the exact scheme and its claimed byte bound:

- Correctness through the actual encode/decode/evaluate path.
- Both artifact-codec round trips and a worst-case serialized byte bound.
- The challenge's forbidden-disclosure theorem in a shared 256-bit ROM.
- If `hidePrivate` is true, indistinguishability for any two private inputs
  producing the same permitted result at the fixed evaluator input.

Exact correctness for all admissible keys, coins, and hash interpretations is
the default. The author may instead select `Correctness.statistical`, with a
nontrivial rational error bound over the experiment. That permits explicitly
bounded failure; it does not permit a contestant to weaken exact correctness.

The ROM profile fixes a query cap and an explicit rational error function below
one throughout that range. Rationals keep the challenge metadata executable;
probability measures remain proof-only. The example bound is `(q+1)/2^128`
through `q = 2^64`, matching the current BLAKE3 target numerically. A certificate
must establish it; choosing the profile supplies no security theorem.

The evaluator knows the input. This initial profile is classical, one-shot,
and static-input; it gives the attacker the authorized output for free. It
does not cover adaptive input selection, multiple releases, quantum queries,
timing leakage, or security of SHA-256 as an ideal oracle. Bounds hold for every
deterministic bounded-query attacker, including every fixed choice of auxiliary
coins; a randomized-attacker lifting theorem is not included here.

All public instance-dependent state must be serialized into the scored artifact.
Fixed compiled program code and the declared disclosure channels are outside
that score; specializing a binary with instance data is not a permitted escape.
Fixed codecs allow a future generic runtime to reject malformed private/input
encodings. The executable methods must compile even though their proof fields
may use noncomputable mathematics.

## Small implementation plan and feasibility

1. **Done here:** one-file contract, executable BLAKE3 declaration and G1
   declaration pattern, meaningful probability/nonvacuity audits, disclosure
   and validity native tests, immutable-base CI integration.
2. **BLAKE3 migration:** adapt the existing byte runner and audit to the new
   declaration; explicitly verify equivalence of bit order, distinct-pair
   sampling, selected output, and the recovery game before changing acceptance.
   This is manageable plumbing. Certifying its half-gates baseline still needs
   complete lowering/transport correctness and its correlated-label ROM proof.
3. **G1 migration:** supply the codecs/reference and preserve function privacy.
   The example also requires opposite-input-label recovery security, which the
   old `FunctionPrivate` predicate does not separately assert. Existing G1
   correctness/ideal-law proofs remain useful, but do not directly certify
   finite-key expansion through the public ROM. Keep its 5,940,480-byte result
   under its existing rules until that additional argument is established.
4. **Executable packaging:** a protected generic CLI should execute a
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
