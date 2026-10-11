"""Measure the current executable before the complete proof graph is ready.

This authoring-only probe first builds the full equality module, then imports
its executable definitions, uses the protected wrapper and CLI, and retains
certificate=None. The
author source checker selects an optimization only after its full equality
module compiled successfully. It never writes an acceptance
report or an exported tool archive. The isolated full verifier still rebuilds
and audits Solution before any actual bundle can be accepted.
"""
import argparse
import json
from pathlib import Path
import sys
import time
from limits import ROOT, REPO, guarded
import boundary


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--construction', choices=('original', 'machine', 'cached', 'lane'), default='original')
    variant = parser.parse_args().construction
    implementation = {
        'original': ('Sharing', 'construction', 'Sharing'),
        'machine': ('MachineImplementation', 'machineConstruction', 'MachineSharing'),
        'cached': ('CachedImplementation', 'cachedConstruction', 'CachedSharing'),
        'lane': ('LaneImplementation', 'laneConstruction', 'LaneSharing'),
    }
    module, construction, proof_module = implementation[variant]
    boundary.check_protected()
    boundary.check_source(ROOT/'WotsLamport/Submission')
    sys.path.insert(0, str(REPO/'secret-release/scripts'))
    from bundle import package
    from test_rust import run_tests
    progress = ROOT/'.yukon/runtime-progress.json'
    progress.parent.mkdir(parents=True, exist_ok=True)
    evidence = dict(diagnosticOnly=True, certificate=None, implementation=variant)
    started = time.monotonic()
    report = ROOT/'.yukon/runtime-probe.json'
    report.unlink(missing_ok=True)

    def record(phase, **details):
        evidence.update(phase=phase, elapsedSeconds=time.monotonic()-started, **details)
        temporary = progress.with_suffix('.tmp')
        temporary.write_text(json.dumps(evidence, indent=2)+'\n')
        temporary.replace(progress)

    record('checking-equality')
    # Prove the complete correspondence before compiling its executable-only
    # module. No optimized binary is built when this proof build fails.
    proof = guarded(['lake', 'build', 'WotsLamport.Submission.'+proof_module], ROOT)
    print(proof['stdout'], end='', flush=True)
    print(proof['stderr'], end='', flush=True)
    record('equality-checked', proofModule=proof_module)
    generated = ROOT/'.lake/generated/SRTools.lean'
    generated.parent.mkdir(parents=True, exist_ok=True)
    previous = generated.read_bytes() if generated.exists() else None
    destination = ROOT/'.yukon/runtime-probe'
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
        print(f'RUNTIME_PROBE: build {variant} executable after checking its equality proofs', flush=True)
        record('building-executable')
        build = guarded(['lake', 'build', 'secret-release-tools'], ROOT)
        record('executable-built', compilerPeakMemoryBytes=build['peakMemoryBytes'])
        print(build['stdout'], end='', flush=True)
        print(build['stderr'], end='', flush=True)
        metadata = package(ROOT, destination)
        assert metadata['status'] == 'uncertified' and metadata['certifiedBytes'] is None
        metadata.update(diagnostic=True, acceptance='not-audited',
                        entrypoint='WotsLamport.Tests.runtimeProbeEntry', implementation=variant)
        (destination/'bundle.json').write_text(json.dumps(metadata, indent=2)+'\n')
        print('RUNTIME_PROBE: run standard SDK integration', flush=True)
        record('checking-sdk')
        measured = run_tests(ROOT, destination)
        record('sdk-passed', native=measured)
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
        record('checking-reference-correspondence')
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
        record('reference-correspondence-passed', independentNativePeakMemoryBytes=independent['peakMemoryBytes'])
        print('PASS: runtime diagnostic only; no complete proof or acceptance result', flush=True)
        print(json.dumps(result), flush=True)
    finally:
        if previous is None:
            generated.unlink(missing_ok=True)
        else:
            generated.write_bytes(previous)


if __name__ == '__main__':
    main()
