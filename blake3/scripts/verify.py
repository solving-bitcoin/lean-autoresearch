"""Isolated, scheme-level proof checking and complete serialized measurement."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile

from resources import ROOT,guarded
from policy import check_protected,check_source,dependencies,score_value
from lean_source_policy import import_modules,code_without_comments_or_strings
from check_runtime import check_reference


def native_description(executable,project):
    r=guarded([executable,'describe'],project,native=True)
    if r['stderr']:raise SystemExit('unexpected submission description side output')
    return json.loads(r['stdout']),r['peakMemoryBytes']


def native_cases(executable,description,project,name):
    description_path=project/f'{name}-description.json'
    description_path.write_text(json.dumps(description))
    result_path=project/f'{name}-result.json'
    r=guarded([sys.executable,ROOT/'scripts/check_runtime.py',executable,
               description_path,project,result_path],project,native=True)
    print(r['stdout'],end='',flush=True)
    return json.loads(result_path.read_text()),r['peakMemoryBytes']


def negative_certificate_check(project):
    path=project/'MissingSecrecy.lean'
    path.write_text('''import Blake3Prize.Protected.Target
open Blake3Prize.Protected
example (s : Scheme) (n : Nat) (h : Correct s) (c : CodecLaws s) (b : ArtifactBound s n) :
    ValidCandidate s n .classicalBoundedQueryROM :=
  { correct := h, codec := c, artifact_bound := b }
''')
    try:
        guarded(['lake','env','lean','-j1',path.name],project)
    except SystemExit as error:
        if 'secret' not in str(error):raise
    else:
        raise SystemExit('missing secrecy field was accepted')
    print('PASS: correctness, codec, and size alone cannot obtain a certificate',flush=True)


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--submission',type=Path,default=ROOT/'Blake3Prize/Submission')
    parser.add_argument('--allow-unranked',action='store_true',
                        help='authoring CI only: check the challenge even when no certified scheme exists')
    parser.add_argument('--authoring-preview',action='store_true',
                        help='PR-owned authoring checks: never emit an accepted score')
    args=parser.parse_args()
    output=ROOT/'.yukon/blake3-64-labeled-hash-score.json'
    if output.exists():output.unlink()
    check_protected();check_source(args.submission);dependencies()
    score=score_value(args.submission/'score.txt')
    r=guarded([sys.executable,ROOT/'scripts/check_policy.py'],native=True)
    print(r['stdout'],end='',flush=True)
    r=guarded([sys.executable,ROOT/'scripts/check_overlay_tests.py'],native=True)
    print(r['stdout'],end='',flush=True)
    with tempfile.TemporaryDirectory(prefix='blake3-certified-') as temporary:
        project=Path(temporary)
        for name in ('lakefile.lean','lake-manifest.json','lean-toolchain','Blake3Prize.lean'):
            shutil.copy2(ROOT/name,project/name)
        for name in ('Protected','Baselines'):
            shutil.copytree(ROOT/'Blake3Prize'/name,project/'Blake3Prize'/name)
        shutil.copy2(ROOT/'Blake3Prize/Main.lean',project/'Blake3Prize/Main.lean')
        (project/'.lake').mkdir()
        (project/'.lake/packages').symlink_to(ROOT/'.lake/packages',target_is_directory=True)
        # Compile selected, pinned proof libraries before any submission source
        # enters the project. This allows optional libraries without treating
        # legitimate new dependency build products as untrusted cache changes.
        imports={'Blake3Prize.Protected.Runner'}
        for source in args.submission.glob('*.lean'):
            for imported in import_modules(code_without_comments_or_strings(source.read_text())):
                if not imported.value.startswith('Blake3Prize.Submission.'):
                    imports.add(imported.value)
        (project/'ProofImports.lean').write_text('\n'.join(f'import {m}' for m in sorted(imports))+
                                               '\n\ndef main : IO Unit := pure ()\n')
        with (project/'lakefile.lean').open('a') as f:
            f.write('\nlean_exe "blake3-proof-imports" where\n  root := `ProofImports\n')
        measurements=[]
        # Elaborate the fresh trusted Lake configuration in its own capped
        # process. Exit before compiling proofs so configuration elaboration's
        # retained memory does not overlap the large imported environments.
        # Only configuration is cached here; all challenge modules below are
        # still rebuilt from source inside this fresh isolated directory.
        r=guarded(['lake','resolve-deps'],project)
        measurements.append(r['peakMemoryBytes'])
        print(f"PASS: isolated Lake configuration; peak {r['peakMemoryBytes']} bytes",flush=True)
        for target in ('blake3-proof-imports','blake3-trusted','blake3-runner-test'):
            r=guarded(['lake','build',target],project)
            measurements.append(r['peakMemoryBytes'])
            print(f"PASS: trusted build {target}; peak {r['peakMemoryBytes']} bytes",flush=True)
        dependencies(snapshot=True)
        shutil.copy2(ROOT/'scripts/BoundaryAudit.lean',project/'BoundaryAudit.lean')
        r=guarded(['lake','env','lean','-j1','BoundaryAudit.lean'],project)
        print(r['stdout'],end='',flush=True)
        negative_certificate_check(project)
        shutil.copytree(args.submission,project/'Blake3Prize/Submission')
        r=guarded(['lake','build','blake3-submission'],project)
        measurements.append(r['peakMemoryBytes'])
        print(f"PASS: submission build; peak {r['peakMemoryBytes']} bytes",flush=True)
        expected='none' if score is None else f'some {score}'
        audit=(ROOT/'scripts/Audit.lean').read_text()+f'''
example : (Blake3Prize.Submission.entry.map (fun c => c.maxBytes)) = {expected} := by rfl
'''
        (project/'Audit.lean').write_text(audit)
        r=guarded(['lake','env','lean','-j1','Audit.lean'],project)
        print(r['stdout'],end='',flush=True);measurements.append(r['peakMemoryBytes'])
        r=guarded([project/'.lake/build/bin/blake3-trusted'],project,native=True)
        native_peaks=[r['peakMemoryBytes']]
        clean_path=project/'clean-checks.json';clean_path.write_text(r['stdout'])
        report=check_reference(clean_path)
        fixture=project/'.lake/build/bin/blake3-runner-test'
        fixture_description,peak=native_description(fixture,project);native_peaks.append(peak)
        fixture_report,peak=native_cases(fixture,fixture_description,project,'runner-test')
        native_peaks.append(peak)
        assert fixture_report['artifactBytes']==49162, 'fixture framing bytes were not all counted'
        report['runnerSelfTestCases']=fixture_report['labelEvaluationCases']
        executable=project/'.lake/build/bin/blake3-submission'
        description,peak=native_description(executable,project);native_peaks.append(peak)
        if score is None:
            if description!={'status':'unranked'}:raise SystemExit('unranked metadata disagrees with Lean entry')
            report.update(status='unranked',score=None,artifactBytes=None,
                          reason='No submission has the complete correctness, codec, size, and secrecy certificate.')
        else:
            if description.get('status')!='certified' or description.get('claimedBytes')!=score:
                raise SystemExit('native description disagrees with kernel-checked score')
            native,peak=native_cases(executable,description,project,'submission')
            native_peaks.append(peak);report.update(native)
            report.update(status='accepted',score=score,securityProfile=description['securityProfile'],
                          maxOracleQueries=description['maxOracleQueries'],oracleOutputBits=description['oracleOutputBits'],
                          failureBound=description['failureBound'],implementationBridge=description['implementationBridge'])
        report.update(compilerPeakMemoryBytes=max(measurements),nativePeakMemoryBytes=max(native_peaks),
                      direction='minimize',unit='bytes',metric='universal_serialized_artifact_byte_bound',
                      protectedDigest=(ROOT/'protected.sha256').read_text().strip(),
                      submissionDigest=hashlib.sha256(b''.join(
                          p.name.encode()+b'\0'+p.read_bytes()+b'\0'
                          for p in sorted(args.submission.iterdir()))).hexdigest())
        dependencies()
        if args.authoring_preview:
            report.update(status='authoring-preview',score=None,
                          candidateClaimBytes=score,
                          reason='PR-owned rules: this run cannot certify submission acceptance.')
        output.parent.mkdir(exist_ok=True)
        output.write_text(json.dumps(report,indent=2)+'\n')
        if args.authoring_preview:
            print(f'AUTHORING PREVIEW ONLY: no accepted score; report {output}',flush=True)
        elif score is None:
            print(f'UNRANKED: contract and runner checks passed; no accepted size. Report: {output}',flush=True)
            if not args.allow_unranked:
                raise SystemExit('No certified entry: --allow-unranked is for challenge-authoring checks only')
        else:
            print(f'ACCEPTED under {description["securityProfile"]}: {score} artifact bytes; report {output}',flush=True)

if __name__=='__main__':main()
