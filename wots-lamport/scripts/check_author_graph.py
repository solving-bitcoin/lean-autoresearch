"""Failure-injection checks for author preview scheduling; no Lean pass implied."""
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from tempfile import TemporaryDirectory
from unittest.mock import patch
import check_lean
import importlib.util
import sys


def fixture(root, cycle=False, optimizations=False, lanes=False):
    directory = root/'WotsLamport/Submission'
    directory.mkdir(parents=True)
    (directory/'A.lean').write_text('import WotsLamport.Submission.B\n')
    (directory/'B.lean').write_text('import WotsLamport.Submission.A\n' if cycle else '')
    (directory/'C.lean').write_text('import WotsLamport.Submission.A\n')
    (directory/'D.lean').write_text('/- import WotsLamport.Submission.C -/\n')
    if optimizations:
        (directory/'MachineSharing.lean').write_text('import WotsLamport.Submission.D\n')
        (directory/'CachedSharing.lean').write_text('import WotsLamport.Submission.MachineSharing\n')
        if lanes:
            (directory/'LaneSharing.lean').write_text('import WotsLamport.Submission.CachedSharing\n')


def exercise(failure=None, cycle=False, optimizations=False, rejected_optimization=None, runtime_probe=True, runtime_construction=None, lanes=False):
    with TemporaryDirectory() as directory:
        root = Path(directory)
        fixture(root, cycle, optimizations, lanes)
        calls = []

        def run(command):
            calls.append(tuple(map(str, command)))
            if command[:2] == ['lake', 'build'] and any(target.endswith('.B') for target in command[2:]) and failure:
                raise SystemExit(failure)
            if command[:2] == ['lake', 'build'] and any(target.endswith('.'+str(rejected_optimization)) for target in command[2:]):
                raise SystemExit('optimization proof failed')
            return dict(stdout='', stderr='', peakMemoryBytes=1)

        with patch.object(check_lean, 'ROOT', root), patch.object(check_lean, 'guarded', run), \
             patch.object(check_lean, 'check_protected'), patch.object(check_lean, 'check_source'), \
             redirect_stdout(StringIO()):
            try:
                arguments = ['--runtime-probe'] if runtime_probe else []
                if runtime_construction:
                    arguments += ['--runtime-construction', runtime_construction]
                check_lean.main(arguments)
            except SystemExit as error:
                import json
                evidence = root/'.yukon/author-sources.json'
                if evidence.exists():
                    data = json.loads(evidence.read_text())
                    assert data['diagnosticOnly'] is True
                    assert any(item['status'] == 'failed' for item in data['modules'])
                return calls, str(error)
            return calls, None


def check_probe_proof_gate(variant):
    import check_runtime_probe as probe
    with TemporaryDirectory() as directory:
        root = Path(directory)
        calls = []
        (root/'.yukon').mkdir()
        report = root/'.yukon/runtime-probe.json'
        report.write_text('STALE SUCCESS')

        def reject_proof(command, *_):
            calls.append(command)
            raise SystemExit('equality proof rejected')

        with patch.object(probe, 'ROOT', root), \
             patch.object(probe.boundary, 'check_protected'), \
             patch.object(probe.boundary, 'check_source'), \
             patch.object(probe, 'guarded', reject_proof), \
             patch.object(sys, 'argv', ['check_runtime_probe.py', '--construction', variant]):
            try:
                probe.main()
            except SystemExit as error:
                assert str(error) == 'equality proof rejected'
            else:
                raise AssertionError('runtime probe ignored proof failure')
        proof = {'machine': 'MachineSharing', 'lane': 'LaneSharing'}[variant]
        assert calls == [['lake', 'build', 'WotsLamport.Submission.'+proof]]
        assert not (root/'.lake/generated/SRTools.lean').exists()
        assert not report.exists(), 'proof failure must clear an older runtime success report'


def check_diagnostic_retention():
    spec = importlib.util.spec_from_file_location('wots_author_verify', Path(__file__).with_name('verify.py'))
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    with TemporaryDirectory() as directory:
        root = Path(directory)
        report = root/'.yukon/author-sources.json'
        report.parent.mkdir()
        report.write_text('STALE')
        progress = root/'.yukon/runtime-progress.json'
        progress.write_text('STALE RUNTIME')
        old_result = root/'.yukon/runtime-probe.json'
        old_result.write_text('STALE SUCCESS')

        def rejected(*_):
            assert not report.exists() and not progress.exists() and not old_result.exists()
            report.write_text('{"diagnosticOnly": true, "modules": []}')
            progress.write_text('{"diagnosticOnly": true, "phase": "checking-sdk"}')
            raise SystemExit('unchanged timeout rejection')

        output = StringIO()
        with patch.object(verifier.boundary, 'ROOT', root), \
             patch.object(verifier.module, 'verify', rejected), \
             patch.object(sys, 'argv', ['verify.py', '--authoring-preview']), \
             redirect_stdout(output):
            try:
                verifier.main()
            except SystemExit as error:
                assert str(error) == 'unchanged timeout rejection'
            else:
                raise AssertionError('diagnostics suppressed rejection')
        assert 'AUTHOR_SOURCE_DIAGNOSTICS' in output.getvalue()
        assert 'RUNTIME_PROGRESS' in output.getvalue() and 'checking-sdk' in output.getvalue()
        assert 'diagnosticOnly' in output.getvalue() and 'STALE' not in output.getvalue()


def check_runtime_progress():
    import json
    import check_runtime_probe as probe
    sys.path.insert(0, str(probe.REPO/'secret-release/scripts'))
    import bundle
    import test_rust
    for failure, expected in [('build', 'building-executable'), ('sdk', 'checking-sdk'),
                              ('reference', 'checking-reference-correspondence'),
                              (None, 'reference-correspondence-passed')]:
        with TemporaryDirectory() as directory:
            root = Path(directory)

            def run(command, *_, **options):
                if command[:2] == ['lake', 'build'] and command[-1] == 'secret-release-tools' and failure == 'build':
                    raise SystemExit('injected build failure')
                if command[0] == '/fake/reference' and failure == 'reference':
                    raise SystemExit('injected reference failure')
                stdout = ''
                if command[0] == 'cargo':
                    stdout = json.dumps(dict(reason='compiler-artifact', executable='/fake/reference',
                                             profile=dict(test=True)))+'\n'
                return dict(stdout=stdout, stderr='', peakMemoryBytes=1)

            def package(_, destination):
                destination.mkdir(parents=True)
                return dict(status='uncertified', certifiedBytes=None)

            def sdk(*_):
                if failure == 'sdk':
                    raise SystemExit('injected sdk failure')
                return dict(pipelineCases=1)

            with patch.object(probe, 'ROOT', root), patch.object(probe, 'guarded', run), \
                 patch.object(probe.boundary, 'check_protected'), patch.object(probe.boundary, 'check_source'), \
                 patch.object(bundle, 'package', package), patch.object(test_rust, 'run_tests', sdk), \
                 patch.object(sys, 'argv', ['check_runtime_probe.py', '--construction', 'lane']), \
                 redirect_stdout(StringIO()):
                try:
                    probe.main()
                except SystemExit as error:
                    assert str(error) == 'injected '+failure+' failure'
                else:
                    assert failure is None
            evidence = json.loads((root/'.yukon/runtime-progress.json').read_text())
            assert evidence['diagnosticOnly'] is True and evidence['certificate'] is None
            assert evidence['phase'] == expected
            assert ('compilerPeakMemoryBytes' in evidence) == (failure != 'build')
            assert ('native' in evidence) == (failure not in ('build', 'sdk'))
            assert (root/'.yukon/runtime-probe.json').exists() == (failure is None)
            assert not (root/'.lake/generated/SRTools.lean').exists()


def main():
    check_runtime_progress()
    check_diagnostic_retention()
    check_probe_proof_gate('machine')
    check_probe_proof_gate('lane')
    calls, error = exercise()
    assert error is None
    assert calls == [('lake', 'build', 'WotsLamport.Submission.B', 'WotsLamport.Submission.D'),
                     ('lake', 'build', 'WotsLamport.Submission.A'),
                     ('lake', 'build', 'WotsLamport.Submission.C')]
    calls, error = exercise('ordinary elaboration failure')
    assert error.startswith('AUTHOR_PROOFS_REJECTED:')
    assert all(f'WotsLamport.Submission.{name}' in error for name in 'BAC')
    assert calls[:3] == [('lake', 'build', 'WotsLamport.Submission.B', 'WotsLamport.Submission.D'),
                         ('lake', 'build', 'WotsLamport.Submission.B'),
                         ('lake', 'build', 'WotsLamport.Submission.D')]
    assert len(calls) == 4 and calls[-1][-1].endswith('/scripts/check_runtime_probe.py')
    for failure in ['aggregate RSS exceeded', 'build timed out']:
        calls, error = exercise(failure)
        assert len(calls) == 1 and error == failure
    calls, error = exercise('ordinary elaboration failure', runtime_probe=False)
    assert error.startswith('AUTHOR_PROOFS_REJECTED:') and len(calls) == 3
    calls, error = exercise(cycle=True)
    assert not calls and error.startswith('AUTHOR_PROOFS_REJECTED: import cycle')
    for rejected, expected in [(None, 'cached'), ('CachedSharing', 'machine'), ('MachineSharing', None)]:
        calls, error = exercise('ordinary elaboration failure', optimizations=True,
                                rejected_optimization=rejected)
        assert error.startswith('AUTHOR_PROOFS_REJECTED:')
        probe = calls[-1]
        if expected is None:
            assert probe[-1].endswith('/scripts/check_runtime_probe.py')
            assert not any(call[-1] == 'WotsLamport.Submission.CachedSharing' for call in calls)
        else:
            assert probe[-2:] == ('--construction', expected)
            selected = 'CachedSharing' if expected == 'cached' else 'MachineSharing'
            assert any(call[-1] == 'WotsLamport.Submission.'+selected for call in calls[:-1])
    for rejected in [None, 'LaneSharing']:
        calls, error = exercise('ordinary elaboration failure', optimizations=True, lanes=True,
                                rejected_optimization=rejected, runtime_construction='lane')
        assert error.startswith('AUTHOR_PROOFS_REJECTED:')
        probes = [call for call in calls if any(part.endswith('/scripts/check_runtime_probe.py') for part in call)]
        if rejected:
            assert not probes, 'a rejected requested proof must not fall back to a known-slow implementation'
        else:
            assert len(probes) == 1 and probes[0][-2:] == ('--construction', 'lane')
            assert any(call[-1] == 'WotsLamport.Submission.LaneSharing' for call in calls)
    calls, error = exercise('ordinary elaboration failure', optimizations=True, runtime_construction='lane')
    assert error.startswith('AUTHOR_PROOFS_REJECTED:')
    assert not any(any(part.endswith('/scripts/check_runtime_probe.py') for part in call) for call in calls)
    print('PASS: all modules on success; failures remain fatal; independent builds continue; resource/cycle failures stop; only compiled optimizations run')


if __name__ == '__main__':
    main()
