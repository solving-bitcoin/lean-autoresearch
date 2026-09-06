"""Fresh local-source compilation, exact certificate/score audit, and native I/O."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
from limits import ROOT, REPO, guarded
from boundary import (check_protected, check_source, dependencies, score_value,
                      SHARED, shared_source_files, REUSED_FILES)
from lean_source_policy import import_modules, code_without_comments_or_strings


def copy_file(source, destination):
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, destination)


def negative_certificate_check(project):
    path = project/'MissingSecrecy.lean'
    path.write_text('''import G1Release.Protected.Target
open SecretRelease G1Release.Protected
example (s : Scheme challenge) (n : Nat) (h : Correct s)
    (d : ∀ a, s.decode (s.encode a) = some a)
    (e : ∀ b a, s.decode b = some a → s.encode a = b)
    (b : ArtifactBound s n) : CertifiedScheme :=
  { scheme := s, maxBytes := n, correct := h,
    decode_encode := d, encode_decode := e, artifactBound := b }
''')
    try:
        guarded(['lake','env','lean','-j1',path.name], project)
    except SystemExit as error:
        if not all(field in str(error) for field in ('releaseSecure','functionPrivate')):
            raise
    else:
        raise SystemExit('incomplete secrecy certificate was accepted')
    print('PASS: correctness, codec, and byte bound alone cannot certify', flush=True)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--submission', type=Path, default=ROOT/'G1Release/Submission')
    parser.add_argument('--allow-unranked', action='store_true')
    parser.add_argument('--authoring-preview', action='store_true')
    args = parser.parse_args()
    state = ROOT/'.yukon'; state.mkdir(exist_ok=True)
    output = state/'g1-release-score.json'
    output.unlink(missing_ok=True)
    check_protected(); check_source(args.submission); dependencies()
    score = score_value(args.submission/'score.txt')
    r = guarded([sys.executable, ROOT/'scripts/check_boundary.py'], native=True)
    print(r['stdout'], end='', flush=True)
    builds, natives = [], [r['peakMemoryBytes']]
    with tempfile.TemporaryDirectory(prefix='g1-release-certified-') as temporary:
        tree = Path(temporary); project = tree/'g1-release'
        shared = tree/'secret-release'; project.mkdir()
        for source in shared_source_files(SHARED):
            copy_file(source, shared/source.relative_to(SHARED))
        for source in REUSED_FILES:
            copy_file(source, tree/source.relative_to(REPO))
        for name in ('lakefile.lean','lake-manifest.json','lean-toolchain','G1Release.lean','G1Release/Main.lean'):
            copy_file(ROOT/name, project/name)
        shutil.copytree(ROOT/'G1Release/Protected', project/'G1Release/Protected')
        shutil.copytree(ROOT/'native', project/'native')
        (project/'.lake').mkdir()
        # Only authenticated external Git dependency caches may be reused.
        (project/'.lake/packages').symlink_to(ROOT/'.lake/packages', target_is_directory=True)
        imports = {'G1Release.Protected.Runner'}
        for source in args.submission.glob('*.lean'):
            for imported in import_modules(code_without_comments_or_strings(source.read_text())):
                if not imported.value.startswith('G1Release.Submission.'):
                    imports.add(imported.value)
        (project/'ProofImports.lean').write_text('\n'.join(f'import {m}' for m in sorted(imports))+
                                               '\n\ndef main : IO Unit := pure ()\n')
        with (project/'lakefile.lean').open('a') as stream:
            stream.write('\nlean_exe "g1-proof-imports" where\n  root := `ProofImports\n')
        r = guarded(['lake','resolve-deps'], project); builds.append(r['peakMemoryBytes'])
        for target in ('g1-release-checks','g1-release-runner-test','g1-proof-imports'):
            r = guarded(['lake','build',target], project)
            builds.append(r['peakMemoryBytes'])
            print(f"PASS: fresh trusted build {target}; peak {r['peakMemoryBytes']} bytes", flush=True)
        dependencies(snapshot=True)
        copy_file(ROOT/'scripts/ContractChecks.lean', project/'ContractChecks.lean')
        r = guarded(['lake','env','lean','-j1','ContractChecks.lean'], project)
        builds.append(r['peakMemoryBytes'])
        negative_certificate_check(project)
        shutil.copytree(args.submission, project/'G1Release/Submission')
        r = guarded(['lake','build','g1-release'], project); builds.append(r['peakMemoryBytes'])
        expected = 'none' if score is None else f'some {score}'
        audit = (ROOT/'scripts/Audit.lean').read_text()+f'''
example : G1Release.Submission.entry.map (fun c => c.maxBytes) = {expected} := by rfl
'''
        (project/'Audit.lean').write_text(audit)
        r = guarded(['lake','env','lean','-j1','Audit.lean'], project)
        builds.append(r['peakMemoryBytes']); print(r['stdout'], end='', flush=True)
        executable = project/'.lake/build/bin/g1-release'
        r = guarded([executable,'describe'], project, native=True); natives.append(r['peakMemoryBytes'])
        if r['stderr']: raise SystemExit('unexpected native description side output')
        description = json.loads(r['stdout'])
        if score is None:
            if description != {'status':'unranked'}: raise SystemExit('entry/score/native status mismatch')
        elif description.get('status') != 'certified' or description.get('claimedBytes') != score:
            raise SystemExit('kernel score and executable description disagree')
        reports = {}
        for name, binary, metadata in (
            ('fixture',project/'.lake/build/bin/g1-release-runner-test',
             {'status':'fixture','randomnessBytes':3,'claimedBytes':32868}),
            ('submission',executable,description)):
            desc = project/f'{name}.json'; desc.write_text(json.dumps(metadata))
            result = project/f'{name}-result.json'
            r = guarded([sys.executable, ROOT/'scripts/check_runtime.py',
                         project/'.lake/build/bin/g1-release-checks',binary,desc,project,result],
                        project, native=True)
            natives.append(r['peakMemoryBytes']); print(r['stdout'], end='', flush=True)
            reports[name] = json.loads(result.read_text())
        if reports['fixture']['observedArtifactBytes'] != 32868:
            raise SystemExit('fixture size was not fully measured')
        dependencies()
        # Keep the exact built binary for download. An unranked binary only
        # describes its status; its garble/evaluate path remains certificate-gated.
        (state/'bin').mkdir(exist_ok=True)
        shutil.copy2(executable, state/'bin/g1-release')
        report = dict(status='unranked' if score is None else 'accepted', score=score,
                      direction='minimize', unit='bytes',
                      metric='universal_serialized_artifact_byte_bound',
                      compilerPeakMemoryBytes=max(builds), nativePeakMemoryBytes=max(natives),
                      protectedDigest=(ROOT/'protected.sha256').read_text().strip(),
                      submissionDigest=hashlib.sha256(b''.join(
                          p.name.encode()+b'\0'+p.read_bytes()+b'\0'
                          for p in sorted(args.submission.iterdir()))).hexdigest(),
                      executableSha256=hashlib.sha256(executable.read_bytes()).hexdigest(),
                      implementationBridge='SHA-256: heuristic / unproved',
                      privatePrivacy='post-release equal-result comparison; not simulation',
                      native=reports)
        if score is not None: report['certificate'] = description
        if args.authoring_preview:
            report.update(status='authoring-preview', score=None, candidateClaimBytes=score,
                          reason='PR-owned authoring rules cannot accept a submission score.')
        elif score is None:
            report['reason'] = 'No complete shared ROM certificate has been submitted.'
        output.write_text(json.dumps(report,indent=2)+'\n')
        print(f"{report['status'].upper()}: {output}", flush=True)
        if score is None and not (args.allow_unranked or args.authoring_preview):
            raise SystemExit('no certified entry; --allow-unranked is authoring-only')

if __name__ == '__main__': main()
