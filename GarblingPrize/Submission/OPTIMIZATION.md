# Norm-seven GLV garbling

The exported construction uses **16,145,129 bytes**, down from the
28,564,459-byte balanced ternary baseline: **12,419,330 bytes saved (43.48%)**.

## Scalar representation

The checked BN254 endomorphism is `phi(x,y) = (beta*x,y)`, with `beta^3 = 1`.
The generator certificate and prime group cardinality prove that `phi`
acts as multiplication by the scalar eigenvalue `lambda` on every G1 point.
Thus the Eisenstein unit `omega` can be evaluated as `phi`.

In the Eisenstein integers, `omega^2 + omega + 1 = 0`, and the radix
`alpha = 3 + omega` has norm `3^2 - 3 + 1 = 7`. The existing reduction and
termination proofs represent every protected scalar with exactly 91 digits
in `{0, ±1, ±omega, ±omega^2}`. Horner evaluation multiplies a point by the
radix using `3*P + phi(P)`.

## Maps and privacy

Each map produces a randomized projective representative of `offset_i + d_i*A`.
Choose 90 independent uniform G1 offsets and solve the first offset so that
their radix-weighted sum is `Q`. Recomposing the 91 map outputs then gives
`Q + r*A` for all protected inputs, including infinity outputs.

The GLV polynomial substitution and eleven-table factorization already have
checked semantics and a privacy change of variables. This submission connects
that construction to the current protected `InternalOracle` contract:

- Each free scalar, nonzero randomizer, chain mask, and table mask uses a
  distinct typed oracle address.
- The standard generator bijects scalar samples with G1. Solving the first
  offset and each final table mask bijects free samples with the constraint
  fibers, proving the exact joint randomness law.
- The existing offset, projective-randomizer, chain-mask, and unused-label-pad
  transformations preserve the artifact bytes and active labels. Pushing the
  derived law through this transformation proves equality of complete public
  view distributions whenever the hidden functions agree at the selected input.

## Exact size and execution

There are 11 affine tables per map. Each table has 254 rows; a pair of rows
contains four 254-bit ciphertexts and occupies exactly 127 bytes. Therefore:

```text
91 maps * 11 tables * 127 row pairs * 127 bytes = 16,145,129 bytes
(161 - 91) maps * 177,419 bytes/map = 12,419,330 bytes saved
```

The codec proves both round trips and rejects truncation and trailing bytes.
Array materialization and the parallel encoder have equality proofs tying
native execution to the same logical artifact. `Solution.validClaimed`
exports the protected `ValidCandidate` theorem for this exact byte bound.
