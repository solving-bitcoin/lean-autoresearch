"""Immutable-base admission across registered submission directories."""
import argparse
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
from projects import projects

p=argparse.ArgumentParser();p.add_argument('--base',type=Path,required=True)
p.add_argument('--candidate',type=Path,required=True);p.add_argument('--base-sha',required=True)
p.add_argument('--head-sha',required=True);p.add_argument('--project',required=True)
p.add_argument('--output',type=Path,required=True)
a=p.parse_args()
base=a.base.resolve(); names=projects(base)
if a.project not in names: raise SystemExit('unregistered challenge')
sys.path.insert(0,str(base/'blake3/scripts'))
import check_overlay as common
prefixes={name:f"{name}/{json.loads((base/name/'challenge.json').read_text())['namespace']}/Submission/" for name in names}
common.PREFIX=prefixes[a.project]
def editable(path):
    for prefix in prefixes.values():
        if path.startswith(prefix):
            tail=path[len(prefix):]
            return tail=='score.txt' or common.MODULE.fullmatch(tail) is not None
    return False
common.editable=editable
print(json.dumps(common.extract(base,a.candidate,a.base_sha,a.head_sha,a.output)))
