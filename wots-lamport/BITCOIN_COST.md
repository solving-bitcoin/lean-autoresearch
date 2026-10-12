# Bitcoin verification size

Locally reproduced against bitcoin-scripts commit
`bf9ee0bb34987a9130ad9dc13a06e18fef137296`, using its locked interpreter
`a09e87af444034698697f0a2267e755cf72f9aed` and whole-leaf compilation policy.
These measurements are not a Lean theorem or a cryptographic certificate.

Both sides authenticate a 256-bit message with SHA-256 and 32-byte secret
preimages and commitments. WOTS uses the exact
`FastWinternitz<32, Sha256, FullWidth>::checksig_verify` generator, followed
by 64 drops and a terminal true. Lamport uses 256 independent two-way pairs,
checks each preimage's width and SHA-256 commitment, and consumes its bit.
Both complete leaves finish with one true item. No HASH160 or shortened
preimages are used. The translation meets the challenge ROM target through
the checked withholding, static-release and separate adaptive-release theorems
and certificate (see [PROOF_STATUS.md](PROOF_STATUS.md)). This does not prove
equivalence with actual Script execution or concrete SHA-256 security.
“256-bit” describes message and hash/preimage widths, not a claim of 256-bit
end-to-end security.

The delivered `Expand` takes the 32-byte message separately and exactly 2,144
signature bytes: 67 full 32-byte chain nodes in chain-index order. The protected
wrapper checks each node against the artifact's public-key endpoints using the
message's 64 high/low nibbles and checksum digits (radices 8,8,16). Canonical
signatures are proved correct for every message. The pinned Bitcoin fixtures
use the same chain nodes and digit convention, transported as 134 stack items
`[minimal ScriptNum digit, 32-byte node]` for chains 0 through 66. The Rust
canonical adapter recovers the typed message/digits and nodes from that form;
`Expand` itself does not parse a Bitcoin witness stack or transaction.

This is tested canonical-profile interoperability, not a theorem covering
all Script-accepted encodings. `Protected/ScriptRelation.lean` keeps actual
Rust/Script equivalence explicitly open. Bridging arbitrary accepted witnesses
requires a proved parser/normalizer and equivalence with the exact interpreter,
flags, ScriptNum semantics and public-key representation. The ROM setup uses
67 independent seeds; no upstream master-seed distribution equivalence is
claimed. None of these boundaries is discharged by the ROM certificate.

| Measured component | WOTS | Lamport |
| --- | ---: | ---: |
| Complete compiled leaf | 5,643 B | 19,457 B |
| Initial data items | 134 | 512 |
| Auxiliary hint items | 0 | 0 |
| Peak combined stack, measured fixtures | 137 | 514 |
| Serialized data witness, maximum | 2,346 B | 8,963 B |
| Complete Taproot witness, maximum | 8,026 B | 28,457 B |
| Incremental witness weight including marker/flag | 8,028 WU | 28,459 WU |
| Incremental witness weight / 4 | 2,007 vB | 7,114.75 vB |
| Whole transaction weight, maximum | 8,404 WU | 28,835 WU |
| **Whole transaction vsize, maximum** | **2,101 vB** | **7,209 vB** |

The common transaction has version 2, one input with empty scriptSig and
final sequence, one P2TR output, and zero locktime. Its stripped serialization
is 94 bytes: 4 + 1 + 41 + 1 + 43 + 4. Each spend has one depth-zero Taproot
leaf, a 33-byte control block, and no annex. The 94-byte base contributes
376 WU on both sides. The marker and flag contribute two more WU.
The full witness includes its count, every item's CompactSize length, the
script and its three-byte length, and the control block and its one-byte
length. Whole vsize is `ceil((376 + 2 + witness_bytes)/4)`.

For WOTS, let z be the number of nonzero canonical digit selectors among
the 67 message/checksum digits. The data witness is `1 + 67*33 + 67 + z`
bytes; complete witness adds `3 + 5643 + 1 + 33`. The upper bound z=67 is
attained by message `21 11 ... 11`: all 64 message nibbles are positive and
checksum 895 has digits 7,7,13. For Lamport, with b one-bits, the data witness
is `3 + 256*33 + 256 + b` bytes; complete witness adds
`3 + 19457 + 1 + 33`. All-ff attains b=256. These maxima concern canonical
witnesses produced by this scheme, not arbitrary padded Script aliases.

| Fixture | WOTS weight / vsize | Lamport weight / vsize |
| --- | ---: | ---: |
| 32 zero bytes | 8,338 / 2,085 | 28,579 / 7,145 |
| 32 ff bytes | 8,401 / 2,101 | 28,835 / 7,209 |
| Bytes 00 through 1f | 8,384 / 2,096 | 28,659 / 7,165 |
| 21 followed by 31 bytes of 11 | 8,404 / 2,101 | 28,643 / 7,161 |

The one universal conversion artifact is **48,752,768 bytes**, comprising
2,144 public-key bytes, a 32-byte nonce, 16,384 label-commitment bytes and
48,734,208 encrypted-share bytes. The Rust end-to-end fixture measured this
size; Lean checked the universal bound in `Layout.artifact_bound` at
`e65c736`. This artifact stays offchain
and is not included in either Bitcoin witness. The WOTS endpoints and Lamport
commitments are included once, as constants in their respective scripts.
The spent outputs have the same size P2TR commitment. Its creation transaction
is outside the spend comparison on both sides.

The raw transactions in `bitcoin-cost-fixtures.json` use a placeholder
outpoint solely for reproducible serialization. They are not broadcastable
transactions. The program verifies Taproot commitments and both strict local
fragment profiles for every fixture, rejects flipped and shortened preimages,
and cross-checks Bitcoin library serialization/weight. Deployment remains
**unclassified**: these profiles do not validate a funded transaction or all
relay policy. Downloading pinned Bitcoin Core 30.3 was blocked by proxy 403;
no Core acceptance is claimed. These leaves authenticate a supplied message;
binding it to the transaction sighash requires a separate protocol and is
not included in either cost.

Reproduce by copying `scripts/bitcoin_cost.rs` to `examples/bitcoin_cost.rs`
in an isolated checkout at the pinned upstream commit, then building with
`cargo build --locked --example bitcoin_cost` and running
`target/debug/examples/bitcoin_cost`. Both commands must use this repository's
`resources.guarded`: 4 GiB local build, 1 GiB native run. The checked local
build peaked at 444,391,424 bytes and the successful native run at 29,409,280.
The generated JSON records complete scripts, witnesses and transactions.

Serialization definitions: [BIP141](https://github.com/bitcoin/bips/blob/master/bip-0141.mediawiki).
Taproot execution boundaries: [BIP342](https://github.com/bitcoin/bips/blob/master/bip-0342.mediawiki).
