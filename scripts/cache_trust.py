#!/usr/bin/env python3
"""Exact-key dependency caches; authenticity comes from the trusted CI writer.

Never snapshot a restored cache before checking it. The seal detects accidental
mixups/tampering, not a malicious writer: GitHub's read-only consumer tokens and
main-only producer are the provenance boundary. Protected modules are rebuilt.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import sys

REPO = Path(__file__).resolve().parents[1]
PROJECTS = ('blake3', 'g1-release', 'wots-lamport')
SCHEMA = 1
SNAPSHOTS = ('trusted-dependency-builds.json', 'trusted-dependency-configs.sha256')

def key(project, repo=REPO):
    if project not in PROJECTS:
        raise SystemExit('CACHE_REJECTED: unknown project')
    h = hashlib.sha256()
    for value in (str(SCHEMA), sys.platform, platform.machine(), project):
        h.update(value.encode() + b'\0')
    paths = [f'{project}/protected.sha256', 'scripts/cache_trust.py',
             'scripts/dependency_builds.py', 'scripts/verifier_common.py',
             'blake3/scripts/policy.py']
    paths += [f'{p}/{n}' for p in (project, 'secret-release')
              for n in ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json')]
    for relative in sorted(set(paths)):
        h.update(relative.encode() + b'\0' + (repo / relative).read_bytes() + b'\0')
    return f'sr-deps-v{SCHEMA}-{project}-{h.hexdigest()}'

def metadata(root, cache_key):
    hashes = {}
    for name in SNAPSHOTS:
        path = root / '.lake' / name
        if not path.is_file() or path.is_symlink():
            raise SystemExit('CACHE_REJECTED: missing or irregular snapshot')
        hashes[name] = hashlib.sha256(path.read_bytes()).hexdigest()
    return {'schema': SCHEMA, 'key': cache_key, 'snapshots': hashes}

def check_seal(root, cache_key):
    path = root / '.lake/ci-cache-manifest.json'
    if not path.is_file() or path.is_symlink():
        raise SystemExit('CACHE_REJECTED: missing or irregular seal')
    if json.loads(path.read_text()) != metadata(root, cache_key):
        raise SystemExit('CACHE_REJECTED: stale key or snapshot bytes')

def boundary(project):
    sys.path.insert(0, str(REPO / project / 'scripts'))
    if project == 'blake3':
        import policy
        return policy
    import boundary as module
    return module

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('operation', choices=('key', 'seal', 'verify'))
    parser.add_argument('project', choices=PROJECTS)
    args = parser.parse_args()
    cache_key = key(args.project)
    if args.operation == 'key':
        print(cache_key)
        return
    root = REPO / args.project
    module = boundary(args.project)
    module.check_protected()
    if args.operation == 'verify':
        check_seal(root, cache_key)
    else:
        if (os.environ.get('GITHUB_REPOSITORY') != 'solving-bitcoin/lean-autoresearch'
            or os.environ.get('GITHUB_REF') != 'refs/heads/main'
            or os.environ.get('GITHUB_EVENT_NAME') not in ('push', 'workflow_dispatch')):
            raise SystemExit('CACHE_REJECTED: only trusted main producer may seal')
    # This reads Git provenance and hashes binaries; it never invokes Lake.
    module.dependencies(snapshot=False)
    if args.operation == 'seal':
        (root / '.lake/ci-cache-manifest.json').write_text(
            json.dumps(metadata(root, cache_key), sort_keys=True) + '\n')
    print(f'PASS: {args.operation} {cache_key}')

if __name__ == '__main__':
    main()
