"""Shared immutable-source verification, audited candidates, and native bundles.

The caller's base-owned overlay authenticates the entire protected tree first.
Digest checking here establishes consistency only, never a PR's authority.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile

from bundle import generate, package, archive
from test_rust import run_tests


def copy(source, destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


def verify(boundary, guarded):
    root=boundary.ROOT; repo=root.parent
    config=json.loads((root/'challenge.json').read_text())
    namespace=config['namespace']; target=f'{namespace}.Protected.challenge'
    parser=argparse.ArgumentParser()
    parser.add_argument('--submission',type=Path,default=root/namespace/'Submission')
    parser.add_argument('--allow-unranked',action='store_true')
    parser.add_argument('--authoring-preview',action='store_true')
    args=parser.parse_args()
    output=root/'.yukon'/config['report']; output.parent.mkdir(exist_ok=True)
    output.unlink(missing_ok=True)
    boundary.check_protected(); boundary.check_source(args.submission); boundary.dependencies()
    score=boundary.score_value(args.submission/'score.txt')
    builds=[]; natives=[]
    from lean_source_policy import import_modules, code_without_comments_or_strings
    r=guarded([sys.executable,repo/'secret-release/scripts/check_framework.py'],root,native=True)
    natives.append(r['peakMemoryBytes']);print(r['stdout'],end='',flush=True)
    for script in config.get('policyTests',[]):
        r=guarded([sys.executable,root/script],root,native=True)
        natives.append(r['peakMemoryBytes']);print(r['stdout'],end='',flush=True)
    if args.authoring_preview:
        for script in config.get('authoringChecks',[]):
            r=guarded([sys.executable,root/script],root)
            builds.append(r['peakMemoryBytes']);print(r['stdout'],end='',flush=True)
    with tempfile.TemporaryDirectory(prefix='secret-release-verified-') as temporary:
        tree=Path(temporary); project=tree/root.name; project.mkdir()
        for source in boundary.protected_files(): copy(source,tree/source.relative_to(repo))
        # These are the only reused Lean objects: authenticated, pinned Git deps.
        (project/'.lake').mkdir()
        (project/'.lake/packages').symlink_to(root/'.lake/packages',target_is_directory=True)
        imports={'SecretRelease.CLI',config['wireModule'],config['fixtureModule']}
        imports.update(config.get('proofModules',[]))
        for source in args.submission.glob('*.lean'):
            imports.update(m.value for m in import_modules(code_without_comments_or_strings(source.read_text()))
                           if not m.value.startswith(namespace+'.Submission.'))
        (project/'ProofImports.lean').write_text('\n'.join('import '+m for m in sorted(imports))+
                                                '\n\ndef main : IO Unit := pure ()\n')
        with (project/'lakefile.lean').open('a') as stream:
            stream.write('\nlean_exe "proof-imports" where\n  root := `ProofImports\n')
        for command in (['lake','resolve-deps'],['lake','build','proof-imports'],
                        ['lake','build','secretRelease/secret-release-checks']):
            r=guarded(command,project);builds.append(r['peakMemoryBytes'])
            print(f"PASS: {' '.join(command)}; peak {r['peakMemoryBytes']} bytes",flush=True)
        shared=tree/'secret-release'
        for audit in ('Audit.lean','SimulationAudit.lean'):
            # Simulation is an explicit optional facade, with no extra certificate claims.
            if audit=='SimulationAudit.lean':
                r=guarded(['lake','build','SecretRelease.Simulation'],project);builds.append(r['peakMemoryBytes'])
            r=guarded(['lake','env','lean','-j1',shared/'SecretReleaseTests'/audit],project)
            builds.append(r['peakMemoryBytes']);print(r['stdout'],end='',flush=True)
        for audit in config.get('audits',[]):
            r=guarded(['lake','env','lean','-j1',project/audit],project)
            builds.append(r['peakMemoryBytes']);print(r['stdout'],end='',flush=True)
        negative=project/'MissingSecrecy.lean'
        negative.write_text(f'''import {namespace}.Protected.Target
open SecretRelease
example (s : Scheme {target}) (n : Nat) (h : Correct s)
    (d : ∀ a, s.decode (s.encode a) = some a)
    (e : ∀ b a, s.decode b = some a → s.encode a = b)
    (b : ArtifactBound s n) : Certificate s n :=
  {{ correct := h, decode_encode := d, encode_decode := e, artifactBound := b }}
''')
        try: guarded(['lake','env','lean','-j1',negative.name],project)
        except SystemExit as error:
            if not all(field in str(error) for field in ('releaseSecure','functionPrivate')): raise
        else: raise SystemExit('incomplete certificate was accepted')
        print('PASS: correctness/codec/size cannot replace the secrecy certificate',flush=True)
        r=guarded([shared/'.lake/build/bin/secret-release-checks'],project,native=True)
        natives.append(r['peakMemoryBytes']); print(r['stdout'],end='',flush=True)
        generate(project,fixture=True)
        r=guarded(['lake','build','secret-release-tools'],project);builds.append(r['peakMemoryBytes'])
        fixture=tree/'fixture';package(project,fixture,fixture=True)
        fixture_tests=run_tests(root,fixture)
        boundary.dependencies(snapshot=True)
        shutil.copytree(args.submission,project/namespace/'Submission')
        generate(project)
        r=guarded(['lake','build','secret-release-tools'],project);builds.append(r['peakMemoryBytes'])
        expected='none' if score is None else f'some {score}'
        audit=(project/config['candidateAudit']).read_text()+f'''
example : ({config['entry']}.bind fun c => c.certified.map (·.maxBytes)) = {expected} := by rfl
'''
        (project/'CandidateAudit.lean').write_text(audit)
        r=guarded(['lake','env','lean','-j1','CandidateAudit.lean'],project)
        builds.append(r['peakMemoryBytes']); print(r['stdout'],end='',flush=True)
        bundle=output.parent/'bundle';metadata=package(project,bundle)
        if metadata['certifiedBytes']!=score: raise SystemExit('binary/kernel/score mismatch')
        if (metadata['status']=='certified') != (score is not None): raise SystemExit('certificate status mismatch')
        candidate_tests=run_tests(root,bundle)
        boundary.dependencies()
        boundary.check_protected()
        submission_hash=hashlib.sha256(b''.join(p.name.encode()+b'\0'+p.read_bytes()+b'\0'
                                              for p in sorted(args.submission.iterdir()))).hexdigest()
        status='authoring-preview' if args.authoring_preview else ('accepted' if score is not None else 'unranked')
        metadata.update(acceptance=status,score=None if args.authoring_preview else score,
                        protectedDigest=(root/'protected.sha256').read_text().strip(),
                        submissionDigest=submission_hash)
        (bundle/'bundle.json').write_text(json.dumps(metadata,indent=2)+'\n')
        archive(bundle)
        report=dict(status=status,score=metadata['score'],candidateStatus=metadata['status'],
                    candidateClaimBytes=metadata['claimedBytes'],direction='minimize',unit='bytes',
                    metric='universal_serialized_artifact_byte_bound',
                    compilerPeakMemoryBytes=max(builds+[fixture_tests['rustBuildPeakMemoryBytes'],candidate_tests['rustBuildPeakMemoryBytes']]),
                    nativePeakMemoryBytes=max(natives+[fixture_tests['rustNativePeakMemoryBytes'],candidate_tests['rustNativePeakMemoryBytes']]),
                    protectedDigest=metadata['protectedDigest'],submissionDigest=submission_hash,
                    native={'fixture':fixture_tests,'submission':candidate_tests},bundle=metadata)
        if score is None: report['reason']='No complete shared ROM certificate; executable tests do not establish secrecy.'
        if args.authoring_preview: report['reason']='PR-owned authoring rules cannot accept a ranked score.'
        output.write_text(json.dumps(report,indent=2)+'\n')
        print(f'{status.upper()}: {output}',flush=True)
        if score is None and not (args.authoring_preview or args.allow_unranked):
            raise SystemExit('no certified entry; unranked mode is authoring-only')
