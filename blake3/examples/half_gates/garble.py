"""Protected 256-bit free-XOR / half-gates backend and exact artifact codec.

The public circuit is fixed before labels, randomness, or inputs are sampled.
This module receives only a public DAG, never executable submission code.
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import secrets
from typing import Callable, Sequence

LABEL_BYTES = 32
INPUT_BITS = 512
OUTPUT_BITS = 256
FIXED_BYTES = 32 + INPUT_BITS * 65 + OUTPUT_BITS * 64
DOMAIN = b'blake3-64-garbling/half-gates/v1\x00'
LabelPairs = Sequence[tuple[bytes, bytes]]


def block(value: int) -> bytes:
    return value.to_bytes(LABEL_BYTES, 'little')


def word(value: bytes) -> int:
    if not isinstance(value, bytes) or len(value) != LABEL_BYTES:
        raise ValueError('labels must contain exactly 32 bytes')
    return int.from_bytes(value, 'little')


def pad(role: int, index: int, key: int) -> int:
    """Public, domain-separated hash; security uses the random-oracle model."""
    data = DOMAIN + bytes([role]) + index.to_bytes(8, 'little') + block(key)
    return int.from_bytes(hashlib.sha256(data).digest(), 'little')


@dataclass(frozen=True)
class Circuit:
    gates: tuple[tuple[bool, int, int], ...]
    outputs: tuple[int, ...]
    claimed_bytes: int

    @classmethod
    def from_json(cls, value: dict) -> 'Circuit':
        if set(value) != {'schemaVersion', 'inputBits', 'outputBits', 'gates', 'outputs', 'claimedBytes'}:
            raise ValueError('unexpected circuit fields')
        if (value['schemaVersion'], value['inputBits'], value['outputBits']) != (1, 512, 256):
            raise ValueError('wrong circuit profile')
        if type(value['claimedBytes']) is not int or value['claimedBytes'] < 0:
            raise ValueError('invalid byte claim')
        if not isinstance(value['gates'], list) or len(value['gates']) > 1_000_000:
            raise ValueError('invalid circuit size')
        gates = []
        for i, gate in enumerate(value['gates']):
            if set(gate) != {'isAnd', 'left', 'right'} or type(gate['isAnd']) is not bool:
                raise ValueError('invalid gate')
            a, b = gate['left'], gate['right']
            if any(type(x) is not int or not 0 <= x < 2 * (513+i) for x in (a, b)):
                raise ValueError('non-topological circuit')
            gates.append((gate['isAnd'], a, b))
        outputs = value['outputs']
        if not isinstance(outputs, list) or len(outputs) != OUTPUT_BITS:
            raise ValueError('wrong output width')
        if any(type(x) is not int or not 0 <= x < 2*(513+len(gates)) for x in outputs):
            raise ValueError('invalid output literal')
        circuit = cls(tuple(gates), tuple(outputs), value['claimedBytes'])
        if circuit.artifact_bytes > circuit.claimed_bytes:
            raise ValueError('actual artifact format exceeds the certified bound')
        return circuit

    @property
    def and_count(self) -> int:
        return sum(gate[0] for gate in self.gates)

    @property
    def artifact_bytes(self) -> int:
        return FIXED_BYTES + self.and_count * 64

    def plain(self, message: bytes) -> bytes:
        if len(message) != 64:
            raise ValueError('BLAKE3 challenge requires exactly 64 bytes')
        wires = [(b >> j) & 1 for b in message for j in range(8)]
        def read(lit: int) -> int:
            return (lit & 1) if lit < 2 else wires[lit//2-1] ^ (lit & 1)
        for is_and, a, b in self.gates:
            wires.append(read(a) & read(b) if is_and else read(a) ^ read(b))
        bits = [read(lit) for lit in self.outputs]
        return bytes(sum(bits[8*i+j] << j for j in range(8)) for i in range(32))


def validate_pairs(pairs: LabelPairs, n: int) -> list[tuple[int, int]]:
    if len(pairs) != n:
        raise ValueError('wrong number of label pairs')
    result = []
    for pair in pairs:
        if len(pair) != 2:
            raise ValueError('each bit needs two labels')
        a, b = map(word, pair)
        if a == b:
            raise ValueError('the two labels of a bit must be distinct')
        result.append((a, b))
    return result


def fresh_pairs(n: int) -> list[tuple[bytes, bytes]]:
    result = []
    for _ in range(n):
        a, b = secrets.token_bytes(32), secrets.token_bytes(32)
        while a == b:
            b = secrets.token_bytes(32)
        result.append((a,b))
    return result


def select_input(pairs: LabelPairs, message: bytes) -> tuple[bytes, ...]:
    if len(message) != 64 or len(pairs) != INPUT_BITS:
        raise ValueError('wrong input width')
    return tuple(pairs[i][(message[i//8] >> (i%8)) & 1] for i in range(INPUT_BITS))


def select_output(pairs: LabelPairs, digest: bytes) -> tuple[bytes, ...]:
    if len(digest) != 32 or len(pairs) != OUTPUT_BITS:
        raise ValueError('wrong output width')
    return tuple(pairs[i][(digest[i//8] >> (i%8)) & 1] for i in range(OUTPUT_BITS))


def garble(circuit: Circuit, input_pairs: LabelPairs, output_pairs: LabelPairs,
           random_bytes: Callable[[int], bytes] = secrets.token_bytes) -> bytes:
    """No input message is available here. All per-instance public data is returned."""
    inputs = validate_pairs(input_pairs, INPUT_BITS)
    outputs = validate_pairs(output_pairs, OUTPUT_BITS)
    delta = word(random_bytes(32)) | 1
    constant = word(random_bytes(32))
    zero_labels = [word(random_bytes(32)) for _ in range(INPUT_BITS)]
    artifact = bytearray(block(constant))
    for i, (k0, k1) in enumerate(inputs):
        selector = (k0 ^ k1).bit_length() - 1
        rows = [0, 0]
        for bit, key in enumerate((k0,k1)):
            rows[(key >> selector) & 1] = zero_labels[i] ^ (delta if bit else 0) ^ pad(0,i,key)
        artifact.append(selector)
        artifact.extend(block(rows[0])); artifact.extend(block(rows[1]))
    def zero(lit: int) -> int:
        underlying = constant if lit < 2 else zero_labels[lit//2-1]
        return underlying ^ (delta if lit & 1 else 0)
    for i, (is_and, a, b) in enumerate(circuit.gates):
        a0, b0 = zero(a), zero(b)
        if not is_and:
            zero_labels.append(a0 ^ b0)
            continue
        ha0, ha1 = pad(1,i,a0), pad(1,i,a0 ^ delta)
        hb0, hb1 = pad(2,i,b0), pad(2,i,b0 ^ delta)
        tg = ha0 ^ ha1 ^ (delta if b0 & 1 else 0)
        te = hb0 ^ hb1 ^ a0
        c0 = ha0 ^ (tg if a0 & 1 else 0) ^ hb0 ^ ((te ^ a0) if b0 & 1 else 0)
        zero_labels.append(c0)
        artifact.extend(block(tg)); artifact.extend(block(te))
    for i, lit in enumerate(circuit.outputs):
        k0 = zero(lit)
        rows = [0,0]
        for bit in range(2):
            key = k0 ^ (delta if bit else 0)
            rows[key & 1] = outputs[i][bit] ^ pad(3,i,key)
        artifact.extend(block(rows[0])); artifact.extend(block(rows[1]))
    result = bytes(artifact)
    if len(result) != circuit.artifact_bytes:
        raise AssertionError('artifact accounting mismatch')
    return result


def evaluate(circuit: Circuit, artifact: bytes, active_labels: Sequence[bytes]) -> tuple[bytes, ...]:
    """Only the exact artifact and 512 active labels enter the evaluator.

Malformed framing is rejected. Authentication against malicious garblers or
invalid active labels is outside this honest one-shot garbling profile.
"""
    if not isinstance(artifact, bytes) or len(artifact) != circuit.artifact_bytes:
        raise ValueError('truncated, trailing, or incorrectly sized artifact')
    if len(active_labels) != INPUT_BITS:
        raise ValueError('expected 512 active input labels')
    cursor = 0
    def take() -> int:
        nonlocal cursor
        out = int.from_bytes(artifact[cursor:cursor+32], 'little')
        cursor += 32
        return out
    constant = take()
    wires = []
    for i, label in enumerate(active_labels):
        key = word(label)
        selector = artifact[cursor]; cursor += 1
        rows = take(), take()
        wires.append(rows[(key >> selector) & 1] ^ pad(0,i,key))
    def active(lit: int) -> int:
        return constant if lit < 2 else wires[lit//2-1]
    for i, (is_and,a,b) in enumerate(circuit.gates):
        ka, kb = active(a), active(b)
        if is_and:
            tg, te = take(), take()
            value = pad(1,i,ka) ^ (tg if ka & 1 else 0)
            value ^= pad(2,i,kb) ^ ((te ^ ka) if kb & 1 else 0)
        else:
            value = ka ^ kb
        wires.append(value)
    result = []
    for i, lit in enumerate(circuit.outputs):
        key = active(lit)
        rows = take(), take()
        result.append(block(rows[key & 1] ^ pad(3,i,key)))
    assert cursor == len(artifact)
    return tuple(result)
