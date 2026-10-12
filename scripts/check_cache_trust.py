"""Regression checks for exact-key cache binding and fail-closed restoration."""
import json
from pathlib import Path
import tempfile
from cache_trust import key, metadata, check_seal, SNAPSHOTS

def rejects(action):
    try:
        action()
    except SystemExit:
        return
    raise AssertionError('accepted a stale or corrupted cache')

with tempfile.TemporaryDirectory() as tmp:
    root = Path(tmp)
    (root / '.lake').mkdir()
    rejects(lambda: check_seal(root, 'key'))
    for name in SNAPSHOTS:
        (root / '.lake' / name).write_text('trusted bytes')
    seal = root / '.lake/ci-cache-manifest.json'
    seal.write_text(json.dumps(metadata(root, 'key')))
    check_seal(root, 'key')
    rejects(lambda: check_seal(root, 'other-key'))
    original = (root / '.lake' / SNAPSHOTS[0]).read_bytes()
    (root / '.lake' / SNAPSHOTS[0]).write_text('modified bytes')
    rejects(lambda: check_seal(root, 'key'))
    (root / '.lake' / SNAPSHOTS[0]).write_bytes(original)
    check_seal(root, 'key')
assert len({key(p) for p in ('blake3', 'g1-release', 'wots-lamport')}) == 3
print('PASS: absent, stale, cross-project and modified cache seals rejected')
