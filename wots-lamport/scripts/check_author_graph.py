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
            if command[:2] == ['lake', 'build'] and command[2].endswith('.B') and failure:
                raise SystemExit(failure)
            if command[:2] == ['lake', 'build'] and command[2].endswith('.'+str(rejected_optimization)):
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


def check_diagnostic_retention():
    spec = importlib.util.spec_from_file_location('wots_author_verify', Path(__file__).with_name('verify.py'))
    verifier = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(verifier)
    with TemporaryDirectory() as directory:
        root = Path(directory)
        report = root/'.yukon/author-sources.json'
        report.parent.mkdir()
        report.write_text('STALE')

        def rejected(*_):
            assert not report.exists()
            report.write_text('{"diagnosticOnly": true, "modules": []}')
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
        assert 'diagnosticOnly' in output.getvalue() and 'STALE' not in output.getvalue()


def main():
    check_diagnostic_retention()
    check_probe_proof_gate('machine')
    check_probe_proof_gate('lane')
    calls, error = exercise()
    assert error is None
    assert [call[-1] for call in calls] == [f'WotsLamport.Submission.{name}' for name in 'BACD']
    calls, error = exercise('ordinary elaboration failure')
    assert error.startswith('AUTHOR_PROOFS_REJECTED:')
    assert all(f'WotsLamport.Submission.{name}' in error for name in 'BAC')
    assert [call[-1] for call in calls[:2]] == ['WotsLamport.Submission.B', 'WotsLamport.Submission.D']
    assert len(calls) == 3 and calls[-1][-1].endswith('/scripts/check_runtime_probe.py')
    for failure in ['aggregate RSS exceeded', 'build timed out']:
        calls, error = exercise(failure)
        assert len(calls) == 1 and error == failure
    calls, error = exercise('ordinary elaboration failure', runtime_probe=False)
    assert error.startswith('AUTHOR_PROOFS_REJECTED:') and len(calls) == 2
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
