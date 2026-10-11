"""Measure the current executable before the complete proof graph is ready.

This authoring-only probe imports a selected implementation together with its
proofs, uses the protected wrapper and CLI, and retains certificate=None. The
author source checker selects an optimization only after its full equality
module compiled successfully. It never writes an acceptance
report or an exported tool archive. The isolated full verifier still rebuilds
and audits Solution before any actual bundle can be accepted.
"""
import argparse
import json
from pathlib import Path
import sys
from limits import ROOT, REPO, guarded
import boundary


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--construction', choices=('original', 'machine', 'cached'), default='original')
    variant = parser.parse_args().construction
    implementation = {
        'original': ('Sharing', 'construction'),
        'machine': ('MachineSharing', 'machineConstruction'),
        'cached': ('CachedSharing', 'cachedConstruction'),
    }
    module, construction = implementation[variant]
    boundary.check_protected()
    boundary.check_source(ROOT/'WotsLamport/Submission')
    sys.path.insert(0, str(REPO/'secret-release/scripts'))
    from bundle import package
    from test_rust import run_tests
    generated = ROOT/'.lake/generated/SRTools.lean'
    generated.parent.mkdir(parents=True, exist_ok=True)
    previous = generated.read_bytes() if generated.exists() else None
    destination = ROOT/'.yukon/runtime-probe'
    report = ROOT/'.yukon/runtime-probe.json'
    report.unlink(missing_ok=True)
    try:
        source = '''import SecretRelease.CLI
import WotsLamport.Protected.Wire
import WotsLamport.Submission.PROBE_MODULE

namespace WotsLamport.Tests
-- Diagnostic only: exactly the research construction, without a certificate.
def runtimeProbeEntry : Option (SecretRelease.Candidate WotsLamport.Protected.challenge) :=
  some (WotsLamport.Protected.Entry.candidate {
    construction := WotsLamport.Submission.PROBE_CONSTRUCTION
    maxBytes := WotsLamport.Submission.artifactBytes
    certificate := none })
end WotsLamport.Tests

def main (args : List String) : IO UInt32 :=
  SecretRelease.CLI.main WotsLamport.Protected.wire WotsLamport.Tests.runtimeProbeEntry args
'''
        generated.write_text(source.replace('PROBE_MODULE', module).replace('PROBE_CONSTRUCTION', construction))
        print(f'RUNTIME_PROBE: build {variant} executable with its equality proofs', flush=True)
        build = guarded(['lake', 'build', 'secret-release-tools'], ROOT)
        print(build['stdout'], end='', flush=True)
        print(build['stderr'], end='', flush=True)
        metadata = package(ROOT, destination)
        assert metadata['status'] == 'uncertified' and metadata['certifiedBytes'] is None
        metadata.update(diagnostic=True, acceptance='not-audited',
                        entrypoint='WotsLamport.Tests.runtimeProbeEntry', implementation=variant)
        (destination/'bundle.json').write_text(json.dumps(metadata, indent=2)+'\n')
        print('RUNTIME_PROBE: run standard SDK integration', flush=True)
        measured = run_tests(ROOT, destination)
        # The standard suite is construction-neutral. This separately invoked
        # author test compares this construction's entire 48 MB artifact with
        # the independent Rust implementation, byte for byte.
        workspace = REPO/'secret-release/rust'
        rust = guarded(['cargo', 'test', '--no-run', '--locked', '--jobs', '1',
                        '--message-format=json', '-p', 'wots-lamport-tests', '--test', 'reference'], workspace)
        binaries = []
        for line in rust['stdout'].splitlines():
            item = json.loads(line)
            if item.get('reason') == 'compiler-artifact' and item.get('executable') and item.get('profile', {}).get('test'):
                binaries.append(item['executable'])
        assert len(set(binaries)) == 1
        print('RUNTIME_PROBE: compare complete reference artifact and later messages', flush=True)
        independent = guarded([binaries[0], '--ignored', 'generated_reference_format_correspondence',
                               '--test-threads=1', '--nocapture'], workspace, native=True)
        print(independent['stdout'], end='', flush=True)
        print(independent['stderr'], end='', flush=True)
        result = dict(status='runtime-diagnostic-only', certificate=None,
                      implementation=variant,
                      independentCorrespondence='passed',
                      independentNativePeakMemoryBytes=independent['peakMemoryBytes'],
                      compilerPeakMemoryBytes=build['peakMemoryBytes'], native=measured)
        report.write_text(json.dumps(result, indent=2)+'\n')
        print('PASS: runtime diagnostic only; no complete proof or acceptance result', flush=True)
        print(json.dumps(result), flush=True)
    finally:
        if previous is None:
            generated.unlink(missing_ok=True)
        else:
            generated.write_bytes(previous)


if __name__ == '__main__':
    main()
