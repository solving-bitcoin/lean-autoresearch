"""Independently parse checked-in Bitcoin serialization and canonical openings.

This is a byte/cryptographic fixture check, not Bitcoin consensus validation.
The Rust generator separately executes the exact complete scripts.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

class Reader:
    def __init__(self, data):
        self.data, self.offset = data, 0

    def read(self, n):
        assert 0 <= n <= len(self.data) - self.offset
        result = self.data[self.offset:self.offset+n]
        self.offset += n
        return result

    def compact(self):
        tag = self.read(1)[0]
        if tag < 253:
            return tag
        n = int.from_bytes(self.read({253: 2, 254: 4, 255: 8}[tag]), 'little')
        assert n >= {253: 253, 254: 65536, 255: 2**32}[tag]
        return n

    def vector(self):
        return self.read(self.compact())

def compact_len(n):
    return 1 if n < 253 else 3 if n < 65536 else 5 if n < 2**32 else 9

def witness_len(items):
    return compact_len(len(items)) + sum(compact_len(len(x)) + len(x) for x in items)

def h(data):
    return hashlib.sha256(data).digest()

def seed(domain, i):
    return h(bytes([domain]) + i.to_bytes(4, 'little'))

def chain(node, n):
    for _ in range(n):
        node = h(node)
    return node

def main():
    report = json.loads((ROOT/'bitcoin-cost-fixtures.json').read_text())
    assert report['upstream_commit'] == 'bf9ee0bb34987a9130ad9dc13a06e18fef137296'
    assert report['offchain_artifact_bytes'] == 2144+32+512*32+256*(1984+1982)*48
    maxima = {}
    for row in report['fixtures']:
        data = list(map(bytes.fromhex, row['data_witness_hex']))
        script = bytes.fromhex(row['script_hex'])
        control = bytes.fromhex(row['control_block_hex'])
        spk = bytes.fromhex(row['script_pubkey_hex'])
        m = bytes.fromhex(row['message_hex'])
        assert len(m) == 32 and len(control) == 33 and len(spk) == 34
        assert control[0] & 254 == 192 and spk[:2] == bytes([81, 32])
        assert row['deployment'] == 'unclassified' and row['hint_items'] == 0
        assert row['data_items'] == len(data) and row['script_bytes'] == len(script)
        assert row['control_bytes'] == len(control)
        assert row['data_witness_bytes'] == witness_len(data)
        expected = data + [script, control]
        assert row['complete_witness_bytes'] == witness_len(expected)
        raw = bytes.fromhex(row['transaction_hex'])
        r = Reader(raw)
        assert r.read(4) == bytes([2,0,0,0])
        assert r.read(2) == bytes([0,1])
        assert r.compact() == 1
        assert r.read(36) == bytes(32) + bytes([255])*4  # placeholder, not a UTXO
        assert r.vector() == b'' and r.read(4) == bytes([255])*4
        assert r.compact() == 1
        assert int.from_bytes(r.read(8), 'little') == 100_000
        assert r.vector() == spk
        start = r.offset
        actual = [r.vector() for _ in range(r.compact())]
        assert actual == expected
        assert r.offset-start == row['complete_witness_bytes']
        assert r.read(4) == bytes(4) and r.offset == len(raw)
        assert len(raw) == row['total_tx_bytes']
        base = len(raw)-row['complete_witness_bytes']-2
        weight = 3*base+len(raw)
        assert base == row['stripped_tx_bytes'] == 94
        assert weight == row['weight'] and (weight+3)//4 == row['vsize']
        assert row['incremental_witness_weight'] == weight-4*base
        is_wots = row['scheme'] == 'WOTS256-SHA256-FullWidth'
        if is_wots:
            digits = [d for b in m for d in (b>>4,b&15)]
            c = 960-sum(digits)
            digits += [c%8, (c//8)%8, c//64]
            assert len(data) == 134
            for i,d in enumerate(digits):
                assert data[2*i] == (bytes([d]) if d else b'')
                assert data[2*i+1] == chain(seed(1,i),d)
            assert row['complete_witness_bytes'] == 7959 + sum(d != 0 for d in digits)
        else:
            assert row['scheme'] == 'Lamport256-SHA256' and len(data) == 512
            bits = [(b>>i)&1 for b in m for i in range(8)]
            for i,b in enumerate(bits):
                assert data[2*i] == (b'\x01' if b else b'')
                assert data[2*i+1] == seed(2,2*i+b)
            assert row['complete_witness_bytes'] == 28201+sum(bits)
        maxima[row['scheme']] = max(maxima.get(row['scheme'], 0), row['vsize'])
    assert len(report['fixtures']) == 8
    assert maxima == {'WOTS256-SHA256-FullWidth': 2101, 'Lamport256-SHA256': 7209}
    print('PASS: eight complete Bitcoin serializations, canonical openings and exact vbyte totals')
    print('NOT CHECKED: funded Bitcoin Core consensus/policy, Lean correctness or ROM security')

if __name__ == '__main__':
    main()
