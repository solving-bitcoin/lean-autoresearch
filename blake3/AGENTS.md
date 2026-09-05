# BLAKE3 challenge boundary

This is a separate challenge from `GarblingPrize`. Only
`Blake3Prize/Submission/*.lean` and its `score.txt` are contestant-editable.
Changes to the challenge itself require a separate authoring PR.

The target is the zk.golf BLAKE3 GF(2) specification specialized to standard
unkeyed hashing of exactly 64 bytes to 32 bytes. Input and output wires have
two independently supplied, distinct 32-byte labels per bit. Evaluation gets
only 512 active labels and must return the 256 selected output labels.

The current ranked track submits symbolic Boolean expressions plus a Lean
semantic certificate. The protected compiler and half-gates backend fix the
cryptographic implementation and count every artifact byte, including both
boundary adapters. Candidates may alter expressions, addition circuits,
factorization, and sharing; they may not change the reference, backend,
external labels, format, randomness, verifier, or dependency pins.

Use `./setup.sh` and `./benchmark.sh`. Both enforce 4 GiB build and 1 GiB native
aggregate RSS caps, timeouts, one Lean thread, and reduced CPU priority.
Never run an uncapped build or benchmark. Run one build or test at a time.

Do not use proof gaps, local axioms, native_decide, unsafe/partial definitions,
FFI, initialization, metaprogram execution, macros, compiler substitution
attributes, namespace overrides, filesystem access, or extra dependencies in
submissions. Keep every commit's subject below 50 characters and explain its
mathematics in the body. Keep the PR open for CI.
