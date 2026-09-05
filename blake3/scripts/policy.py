"""Frozen host boundary, source policy, and dependency provenance."""
import hashlib
import json
from pathlib import Path
import re
import sys

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent
sys.path.insert(0,str(REPO/'scripts'))
import check_submission as source_policy
from dependency_builds import write_snapshot,verify_snapshot
from verify_submission import verify_dependency_sources

SNAPSHOT=ROOT/'.lake/trusted-dependency-builds.json'
CONFIG_SNAPSHOT=ROOT/'.lake/trusted-dependency-configs.sha256'


def prepare_generated_cache_excludes():
    # Dependencies can differ in whether they ignore Lake's generated files.
    # Keep source files unchanged and exclude only the two authenticated caches.
    for package in json.loads((ROOT/'lake-manifest.json').read_text())['packages']:
        exclude=ROOT/'.lake/packages'/package['name']/'.git/info/exclude'
        previous=exclude.read_text() if exclude.exists() else ''
        additions=[p for p in ('/.lake/build/','/.lake/config/') if p not in previous.splitlines()]
        if additions:
            exclude.parent.mkdir(parents=True,exist_ok=True)
            exclude.write_text(previous+'\n'+'\n'.join(additions)+'\n')


def config_digest(packages,entries):
    # Lean 4.28 caches compiled lakefiles outside .lake/build. Authenticate
    # these as well as the shared helper's compiled module/object snapshot.
    h=hashlib.sha256()
    for entry in sorted(entries,key=lambda e:e['name']):
        directory=packages/entry['name']/'.lake/config'
        if directory.is_symlink():raise SystemExit('symlink in dependency configuration')
        if not directory.exists():continue
        for p in sorted(directory.rglob('*')):
            if p.is_symlink():raise SystemExit('symlink in dependency configuration')
            if p.is_file():
                h.update(str(p.relative_to(packages)).encode()+b'\0')
                h.update(p.stat().st_size.to_bytes(16,'big'))
                with p.open('rb') as stream:
                    while chunk:=stream.read(1024*1024):h.update(chunk)
    return h.hexdigest()


def protected_files():
    paths=[p for p in ROOT.rglob('*') if p.is_file()
           and not any(part in ('.lake','.yukon','__pycache__') for part in p.relative_to(ROOT).parts)
           and 'Submission' not in p.relative_to(ROOT).parts
           and p.name!='protected.sha256']
    paths.extend(REPO/'scripts'/name for name in (
        'run_with_rss.py','verify_submission.py','check_submission.py','lean_source_policy.py',
        'dependency_builds.py','protected_tree.py','render_benchmark_challenge.py'))
    workflow=REPO/'.github/workflows/blake3.yml'
    if workflow.exists():paths.append(workflow)
    return sorted(set(paths))


def digest():
    h=hashlib.sha256()
    for p in protected_files():
        if p.is_symlink():raise SystemExit('symlink in protected sources')
        h.update(str(p.relative_to(REPO)).encode()+b'\0'+p.read_bytes()+b'\0')
    return h.hexdigest()


def check_protected():
    if (ROOT/'protected.sha256').read_text().strip()!=digest():
        raise SystemExit('BLAKE3_PROTECTED_REJECTED: frozen source digest mismatch')


def check_source(submission):
    source_policy.VERIFIER_OWNED_NAMESPACES=(('Blake3Prize','Protected'),)
    source_policy.allowed_import=lambda m: m=='Blake3Prize.Protected.Target' or m.startswith('Blake3Prize.Submission.') or m=='Mathlib' or m.startswith('Mathlib.')
    source_policy.FORBIDDEN_IDENTIFIERS |= {'attribute','csimp','native_decide','setEnv','modifyEnv'}
    source_policy.check_submission(Path(submission))
    for p in Path(submission).glob('*.lean'):
        code=source_policy.code_without_comments_or_strings(p.read_text())
        if re.search(r'(?m)^\s*#',code) or '«' in code or '»' in code:
            raise SystemExit('BLAKE3_SOURCE_REJECTED: commands/quoted identifiers in submission')


def dependencies(snapshot=False):
    entries=json.loads((ROOT/'lake-manifest.json').read_text())['packages']
    packages=ROOT/'.lake/packages'
    verify_dependency_sources(packages,entries)
    toolchain=(ROOT/'lean-toolchain').read_text().strip()
    config=config_digest(packages,entries)
    if snapshot:
        write_snapshot(SNAPSHOT,packages,entries,toolchain)
        CONFIG_SNAPSHOT.write_text(config+'\n')
    else:
        verify_snapshot(SNAPSHOT,packages,entries,toolchain)
        if not CONFIG_SNAPSHOT.is_file() or CONFIG_SNAPSHOT.is_symlink() or CONFIG_SNAPSHOT.read_text().strip()!=config:
            raise SystemExit('BLAKE3_DEPENDENCY_REJECTED: compiled Lake configuration changed')

if __name__=='__main__':
    if len(sys.argv)>1 and sys.argv[1]=='freeze':
        (ROOT/'protected.sha256').write_text(digest()+'\n')
    else:
        check_protected()
        check_source(ROOT/'Blake3Prize/Submission')
        print('PASS: frozen BLAKE3 boundary and submission source policy')
