"""Base-owned admission of a submission-only Git tree; no candidate code runs.

The pull_request_target workflow checks out its immutable base revision and
executes THIS base copy. Candidate paths, including workflows and digests, are
data only. After comparing complete Git trees, copy only regular submission
blobs to a new directory for the base verifier. Never overlay candidate rules.
"""
import argparse
import json
from pathlib import Path
import re
import subprocess

PREFIX = 'blake3/Blake3Prize/Submission/'
MODULE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*\.lean")
SHA = re.compile(r'[0-9a-f]{40}')
MAX_FILES = 1000
MAX_FILE_BYTES = 4 * 1024**2
MAX_TOTAL_BYTES = 10 * 1024**2


def reject(reason):
    raise SystemExit(f'BLAKE3_OVERLAY_REJECTED: {reason}')


def git(repo, *args):
    return subprocess.check_output(['git', '-C', str(repo), *args], timeout=30)


def tree(repo, revision):
    if not SHA.fullmatch(revision):
        reject('expected an immutable 40-character commit SHA')
    if git(repo, 'rev-parse', 'HEAD').decode().strip() != revision:
        reject('checkout does not match the event commit SHA')
    entries = {}
    for record in git(repo, 'ls-tree', '-rz', '--full-tree', revision).split(b'\0'):
        if not record:
            continue
        metadata, path = record.split(b'\t', 1)
        mode, kind, oid = metadata.decode('ascii').split()
        entries[path.decode('utf-8')] = (mode, kind, oid)
    return entries


def editable(path):
    if not path.startswith(PREFIX):
        return False
    name = path[len(PREFIX):]
    return name == 'score.txt' or MODULE.fullmatch(name) is not None


def admitted_entries(base, candidate):
    changed = sorted(p for p in base.keys() | candidate.keys()
                     if base.get(p) != candidate.get(p))
    protected = [p for p in changed if not editable(p)]
    if protected:
        reject('changes outside the submission boundary: ' + ', '.join(protected[:12]))
    submission = {p: e for p, e in candidate.items() if p.startswith(PREFIX)}
    if not {PREFIX + 'Solution.lean', PREFIX + 'score.txt'} <= submission.keys():
        reject('Solution.lean and score.txt are required')
    if len(submission) > MAX_FILES:
        reject('too many submission files')
    for path, (mode, kind, _) in submission.items():
        if not editable(path) or (mode, kind) != ('100644', 'blob'):
            reject('submission must contain only flat, regular Lean/score files')
    return submission


def extract(base_repo, candidate_repo, base_sha, head_sha, output):
    entries = admitted_entries(tree(base_repo, base_sha), tree(candidate_repo, head_sha))
    total = 0
    for _, _, oid in entries.values():
        size = int(git(candidate_repo, 'cat-file', '-s', oid))
        total += size
        if size > MAX_FILE_BYTES or total > MAX_TOTAL_BYTES:
            reject('submission source byte limit exceeded')
    # Refuse reuse, including symlinks, so no stale source is admitted.
    output.mkdir(parents=True, exist_ok=False)
    for path, (_, _, oid) in entries.items():
        (output / path[len(PREFIX):]).write_bytes(git(candidate_repo, 'cat-file', 'blob', oid))
    return {'trustedBaseSha': base_sha, 'candidateHeadSha': head_sha,
            'submissionFiles': len(entries), 'submissionSourceBytes': total}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--base', type=Path, required=True)
    parser.add_argument('--candidate', type=Path, required=True)
    parser.add_argument('--base-sha', required=True)
    parser.add_argument('--head-sha', required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    provenance = extract(args.base, args.candidate, args.base_sha, args.head_sha, args.output)
    print('PASS: immutable base owns every verifier/rule/dependency/workflow file')
    print(json.dumps(provenance, sort_keys=True))


if __name__ == '__main__':
    main()
