"""Read author-owned project names; optional head tree is inert data only."""
import argparse
import json
from pathlib import Path
import re
import sys

def projects(repo):
    names=json.loads((repo/'secret-release/challenges.json').read_text())
    if not isinstance(names,list) or not names or len(names)!=len(set(names)) or not all(
        isinstance(n,str) and re.fullmatch(r'[a-z][a-z0-9-]*',n) for n in names):
        raise SystemExit('invalid protected project registry')
    return names

def changed_projects(base,candidate,base_sha,head_sha):
    sys.path.insert(0,str(base/'blake3/scripts'))
    from check_overlay import tree
    before,after=tree(base,base_sha),tree(candidate,head_sha)
    changed={p for p in before.keys()|after.keys() if before.get(p)!=after.get(p)}
    names=projects(base)
    selected=[]
    for name in names:
        namespace=json.loads((base/name/'challenge.json').read_text())['namespace']
        prefix=f'{name}/{namespace}/Submission/'
        if any(path.startswith(prefix) for path in changed): selected.append(name)
    # Protected-only authoring PRs must fail trusted admission rather than vanish.
    return selected or names

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--base',type=Path,default=Path(__file__).resolve().parents[2])
    p.add_argument('--candidate',type=Path);p.add_argument('--base-sha');p.add_argument('--head-sha')
    a=p.parse_args()
    print(json.dumps(changed_projects(a.base,a.candidate,a.base_sha,a.head_sha) if a.candidate else projects(a.base)))
