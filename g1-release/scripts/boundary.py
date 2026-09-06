"""Reuse the reviewed host boundary with a separately frozen G1 root."""
import hashlib
import re
import sys
from pathlib import Path
from limits import ROOT, REPO
import policy as common

SHARED = REPO/'secret-release'
# The existing helper's algorithms are shared; these locations are author-owned.
common.ROOT, common.REPO, common.SHARED = ROOT, REPO, SHARED
common.SNAPSHOT = ROOT/'.lake/trusted-dependency-builds.json'
common.CONFIG_SNAPSHOT = ROOT/'.lake/trusted-dependency-configs.sha256'
dependencies = common.dependencies
dependency_entries = common.dependency_entries
prepare_generated_cache_excludes = common.prepare_generated_cache_excludes
shared_source_files = common.shared_source_files
score_value = common.score_value

MATH_FILES = [REPO/'GarblingPrize/Protected'/name for name in
              ('BN254.lean','PrimeCertificates/Base.lean','G1.lean','Bytes.lean')]
REUSED_FILES = MATH_FILES

def protected_files():
    paths = [p for p in ROOT.rglob('*')
             if not any(x in ('.lake','.yukon','__pycache__','Submission') for x in p.relative_to(ROOT).parts)
             and p.name != 'protected.sha256']
    paths += shared_source_files(SHARED) + REUSED_FILES
    paths += [REPO/'blake3/scripts'/n for n in ('resources.py','policy.py','check_overlay.py')]
    paths += [REPO/'scripts'/n for n in ('run_with_rss.py','verify_submission.py',
              'check_submission.py','lean_source_policy.py','dependency_builds.py',
              'protected_tree.py','render_benchmark_challenge.py')]
    paths += list((REPO/'.github/workflows').glob('g1-release*.yml'))
    for p in paths:
        if p.is_symlink(): raise SystemExit('G1_RELEASE_PROTECTED_REJECTED: symlink')
    return sorted(set(p for p in paths if p.is_file()))

def digest():
    h = hashlib.sha256()
    for p in protected_files():
        h.update(str(p.relative_to(REPO)).encode()+b'\0'+p.read_bytes()+b'\0')
    return h.hexdigest()

def check_protected():
    # Consistency only. Immutable-base tree admission is the trust anchor.
    if (ROOT/'protected.sha256').read_text().strip() != digest():
        raise SystemExit('G1_RELEASE_PROTECTED_REJECTED: frozen source digest mismatch')

def check_source(submission):
    policy = common.source_policy
    policy.VERIFIER_OWNED_NAMESPACES = (('G1Release','Protected'),('GarblingPrize',),('SecretRelease',))
    pure_math = {'GarblingPrize.Protected.'+n for n in ('BN254','G1','PrimeCertificates.Base','Bytes')}
    policy.allowed_import = lambda m: (m in pure_math or m in {
        'G1Release.Protected.Target','G1Release.Protected.Codecs',
        'SecretRelease','SecretRelease.Simulation','SecretRelease.Examples'} or
        m.startswith(('G1Release.Submission.','Mathlib.','CompPoly.','VCVio.OracleComp.QueryTracking.',
                      'VCVio.OracleComp.SimSemantics.','VCVio.EvalDist.')) or m == 'Mathlib')
    policy.FORBIDDEN_IDENTIFIERS |= {'attribute','csimp','wf_preprocess','native_decide',
                                   'setEnv','modifyEnv','panic','dbg_trace','include_str'}
    policy.check_submission(Path(submission))
    for p in Path(submission).glob('*.lean'):
        code = policy.code_without_comments_or_strings(p.read_text())
        if re.search(r'(?m)^\s*#',code) or '«' in code or '»' in code:
            raise SystemExit('G1_RELEASE_SOURCE_REJECTED: commands/quoted identifiers')

if __name__ == '__main__':
    if sys.argv[1:] == ['freeze']:
        (ROOT/'protected.sha256').write_text(digest()+'\n')
    else:
        check_protected(); check_source(ROOT/'G1Release/Submission')
        print('PASS: G1 release protected digest and source policy')
