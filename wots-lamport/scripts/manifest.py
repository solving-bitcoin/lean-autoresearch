"""Preserve reviewed manifest bytes only after proving JSON data unchanged."""
import json

def restore_format(path, frozen):
    current = path.read_bytes()
    if json.loads(current) != json.loads(frozen):
        raise SystemExit('WOTS_MANIFEST_REJECTED: Lake changed pinned dependency data\n'
                         + current.decode())
    if current != frozen:
        path.write_bytes(frozen)
        print('PASS: restored manifest formatting; dependency data is identical', flush=True)
