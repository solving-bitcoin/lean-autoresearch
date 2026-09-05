# BLAKE3 conditional-release challenge

Minimize the **complete serialized artifact** for standard, unkeyed BLAKE3:
exactly **64 input bytes → 32 digest bytes**, with two independently supplied,
distinct **32-byte labels** for each of the 512 input and 256 output bits.

The evaluator knows the plaintext message and can compute its digest. It must
receive the correct selected output labels without recovering **any of the 512
opposite input labels or 256 opposite output labels**. Input/digest hiding is
not required. Bit order is byte-major, least-significant-bit first.

```text
construct(randomness, inputLabelPairs, outputLabelPairs) → serializedArtifact
evaluate(serializedArtifact, knownMessage, 512 activeInputLabels) → 256 activeOutputLabels
```

Construction receives no message. Evaluation receives no private label pairs,
construction randomness, hidden state, auxiliary instance files, or output
decoder. A fixed public hash primitive is available to both algorithms, but
using it is optional. Submissions own their **artifact type, construction,
evaluator, encoder, decoder, and proofs**. There is no required circuit,
expression language, lowerer, gate count, half-gates layout, or Yao backend.

## What acceptance checks

[Core.lean](Blake3Prize/Protected/Core.lean) defines the functional interface.
[Target.lean](Blake3Prize/Protected/Target.lean) requires a `ValidCandidate`
certificate containing all four obligations:

1. **Serialized correctness:** for every message, every randomness tape, all
   distinct caller-supplied label pairs, and every interpretation of the public
   hash, decoding and evaluating the serialized construction returns exactly
   the supplied labels selected by the reference BLAKE3 digest.
2. **Codec laws:** both `decode (encode a) = some a` and
   `decode bytes = some a → encode a = bytes`. Instance state cannot survive
   through an uncounted in-memory artifact representation.
3. **Universal size:** the actual `ByteArray.size` of every encoded construction
   is at most the submitted byte claim. Tests additionally measure real files.
4. **Secrecy:** the common conditional-release winning predicate must satisfy
   a protected, reviewed proof profile. Correctness alone cannot qualify.

A submission exports `entry : Option CertifiedScheme`. A certified entry carries
the scheme, literal byte bound, profile, and certificate together. The verifier
kernel-checks that the bound equals `score.txt`, audits the axiom closure, and
executes **those same submitted Lean functions** in fresh processes. It never
substitutes the optional Python garbler for the submitted evaluator.

## Common secrecy rule and the initial ROM profile

[SecretRelease.lean](Blake3Prize/Protected/SecretRelease.lean) defines the public
view and winning rule without naming a cryptographic construction or model.
The view contains the message, artifact, active input labels, and selected
output labels. The attacker wins by returning the correct value and index of
**any one of the 768 opposite labels**. The selected outputs are supplied for
free, so the guarantee does not depend on charging for honest evaluation.

The initially admitted profile is **ClassicalBoundedQueryROM**, defined in
[ROM.lean](Blake3Prize/Protected/ROM.lean). It uses pinned
[VCVio](https://github.com/Verified-zkEVM/VCVio/tree/ffd0ca198fe6e640c0dd7f0f9c599943caacbf64)
`OracleComp`, `simulateQ`, and `IsTotalQueryBound`:

- Label pairs are uniformly sampled ordered **distinct** 256-bit pairs,
  independently across all 768 positions and independently of construction coins.
- The oracle is a uniform random function from finite byte strings to 32-byte
  labels. A byte string is represented by its entire byte list, including its
  length. There are no implicit gate IDs or prescribed domain separators;
  constructions choose and prove their own encodings.
- Construction and attacker share **one** sampled oracle. Repeated queries have
  identical answers. The probability law is Mathlib's countable product measure;
  VCVio interprets each attacker against that same function. It is not the
  uncached semantics that would resample every repeated query.
- The classical attacker may use arbitrary local computation. Its adaptive
  oracle accesses must satisfy VCVio's explicit worst-case query bound.
- The fixed acceptance floor is, for every `0 ≤ q ≤ 2^64`,
  **`Pr[recover any opposite label] ≤ (q + 1) / 2^128`**. This is a concrete
  128-bit query-work floor, not a claim of 256-bit security merely because
  labels have 256 bits. Submissions may prove tighter bounds as well.

The known message is fixed independently of the sampled labels, coins, and
oracle. This initial profile does not claim adaptive message-selection security.
It is a one-shot **label-recovery** guarantee. It does not assert that every
bit of an opposite label is individually hidden, promise multiple input-label
sets under one artifact, or model timing, memory leakage, or quantum queries.
The distribution is a probability measure, and a checked theorem rules out a
certificate for a construction that always exposes an opposite label to a
zero-query attacker.

ROM is one admitted proof profile, not the definition of the common winning
rule. Other profiles can use the same rule with separately reviewed games and
assumptions (for example a PRF reduction). A submission cannot invent an empty
adversary class, weaken the winning rule, or assume its own security theorem.
Adding a profile changes the protected registry through challenge review.

The executable optional hash is Clean's pure Lean SHA-256 specification.
**The ROM theorem contains no SHA-256 assumption or SHA-256 implementation.**
The implementation profile explicitly records the substitution:

```text
Ideal primitive: uniform random function, byte strings → 256 bits
Executable primitive: SHA-256
Ideal-to-concrete bridge: heuristic / unproved
```

A ROM certificate proves its bound in the ideal model. It does not prove that
collision resistance or preimage resistance of SHA-256 suffices to instantiate
that model. Native hash-vector checks validate implementation behavior only.

## Complete byte accounting

The score is the proved worst-case length of the one serialized artifact.
Headers, translation data, keys, tables, commitments, per-instance programs,
and any required public auxiliary state belong in that byte string. Fixed
public program code can be shared across instances; instance-dependent public
data cannot be hidden in a separate code or topology file.

The 16,384-byte active-input channel and 8,192-byte active-output channel are
fixed and excluded from the artifact score. Reports separately show the
24,576 active-label bytes and 64 bytes of already-known message input, plus
`totalIOBytes = measuredArtifactBytes + 24,640`. Private label pairs and an
oblivious-transfer protocol are outside this interface.

## Reference and optional baseline

The reference calls `Clean.Specs.BLAKE3.compress` from the MIT-licensed
[Clean revision 93c9d1e](https://github.com/Verified-zkEVM/clean/blob/93c9d1ef45be9f687214625d7857889cf2485504/Clean/Specs/BLAKE3.lean).
It uses the standard IV, counter 0, block length 64, flags
`CHUNK_START | CHUNK_END | ROOT = 11`, and the first eight output words.
This is the standard 32-byte hash of a 64-byte message. The official BLAKE3
vector and 516 direct Clean byte/bit cases cross-check the specialization.
Attributions for Clean and Apache-2.0 VCVio are retained in
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

The previous implementation is now an **optional, uncertified baseline** in
[Baselines/HalfGates](Blake3Prize/Baselines/HalfGates) and
[examples/half_gates](examples/half_gates). Its expression proofs and local
half-gates identity remain available as optional libraries. Neither the core
contract nor its secrecy profile imports those modules.

Its last measured artifact was **707,680 bytes**:
`32 + 512×65 + 10,281×64 + 256×64 = 707,680`.
That is a measurement of this particular implementation. It lacks the full
serialized-correctness and secrecy certificates required by the new contract,
so **there is currently no ranked submission**. CI displays its measurement
separately and cannot turn it into an accepted scheme-level score.

## Run safely

Lean **4.33.1**, Clean, VCVio, PolyFun, and Mathlib are pinned. With `elan`,
Python 3, Git, and a C compiler installed:

```bash
./blake3/setup.sh
./blake3/benchmark.sh                  # requires a certified entry
./blake3/benchmark.sh --allow-unranked # challenge-authoring checks only
python3 blake3/scripts/baseline.py     # optional, never an accepted score
```

All builds and native checks are sequential, use one Lean thread and reduced
CPU priority, and fail closed if the memory monitor is unavailable. Builds
have a **4 GiB aggregate RSS cap** and 30-minute timeout. Native checks have a
**1 GiB aggregate RSS cap** and five-minute timeout. The common file-size limit
is 2 GiB, working-directory limit 64 GiB, and process limits 64/32 respectively.
Never bypass the wrappers on a development machine.

The verifier imports only pinned trusted modules before compiling submitted
code, then checks the exact certificate and axiom closure (`propext`,
`Classical.choice`, `Quot.sound` only). It checks that correctness/codec/size
without secrecy is rejected. An explicitly insecure fixture tests the generic
binary runner and custom framing; passing those native tests does not make
that fixture eligible for ranking.

Contestant changes belong in `Blake3Prize/Submission/*.lean` and `score.txt`.
The protected reference, profile, runner, dependencies, resource policy, and
workflow belong to challenge authors. The G1 challenge remains separate.
