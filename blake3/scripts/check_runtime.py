"""Exercise the submitted Lean scheme; no cryptographic backend is prescribed."""
import json
from pathlib import Path
import secrets
import tempfile

from resources import ROOT,guarded
from reference import hash64


def check_reference(clean_path):
    data=json.loads(Path(clean_path).read_text())
    vector=json.loads((ROOT/'tests/official-vector.json').read_text())
    # The stored official vector has a provenance record and fixed input/digest.
    message=bytes(range(64))
    expected=bytes.fromhex('4eed7141ea4a5cd4b788606bd23f46e212af9cacebacdc7d1f4c6dc7f2511b98')
    assert hash64(message)==expected
    assert expected.hex() in json.dumps(vector)
    for case in data['references']:
        assert hash64(bytes(case['input']))==bytes(case['digest']), 'Clean reference mismatch'
    if 'hashes' in data:
        import hashlib
        for case in data['hashes']:
            assert hashlib.sha256(bytes(case['input'])).digest()==bytes(case['digest']), 'native public hash mismatch'
    return {'cleanReferenceCases':len(data['references']),
            'nativeHashCases':len(data.get('hashes',[])),
            'referenceModule':'Clean.Specs.BLAKE3',
            'cleanRevision':'93c9d1ef45be9f687214625d7857889cf2485504',
            'referenceLicense':'MIT'}


def fresh_pairs(n):
    result=[]
    for _ in range(n):
        a=secrets.token_bytes(32)
        b=secrets.token_bytes(32)
        while a==b:b=secrets.token_bytes(32)
        result.append((a,b))
    return result


def select(pairs,message):
    return b''.join(pair[(message[i//8]>>(i%8))&1] for i,pair in enumerate(pairs))


def check_scheme(executable,description,directory):
    """Binary protocol limits evaluator inputs to artifact and active labels.
    Secret sampling and expected-output selection live outside the evaluator.
    This is an implementation check; acceptance separately requires the proof.
    """
    executable=Path(executable).resolve()
    directory=Path(directory)
    artifact_sizes=[]
    peaks=[]
    cases=0
    for iteration in range(2):
        with tempfile.TemporaryDirectory(prefix='garbler-',dir=directory) as private:
            private=Path(private)
            inputs,outputs=fresh_pairs(512),fresh_pairs(256)
            if description['randomnessBytes']>2*1024**3:
                raise SystemExit('native randomness exceeds the common 2 GiB file limit')
            with (private/'coins.bin').open('wb') as stream:
                remaining=description['randomnessBytes']
                while remaining:
                    amount=min(remaining,256*1024)
                    stream.write(secrets.token_bytes(amount))
                    remaining-=amount
            (private/'pairs.bin').write_bytes(b''.join(a+b for a,b in inputs+outputs))
            artifact_path=directory/f'artifact-{iteration}.bin'
            r=guarded([executable,'garble',private/'coins.bin',private/'pairs.bin',artifact_path],private,native=True)
            peaks.append(r['peakMemoryBytes'])
            assert not r['stderr'], 'unexpected constructor side output'
            size=artifact_path.stat().st_size
            assert size==json.loads(r['stdout'])['artifactBytes']
            assert size<=description['claimedBytes'], 'actual serialized artifact exceeds proved bound'
        # Pair and coin files have been deleted before evaluator processes start.
        artifact_sizes.append(size)
        messages=[bytes(64),bytes([255])*64,bytes(range(64)),bytes([0x55,0xaa])*32,
                  secrets.token_bytes(64),secrets.token_bytes(64)]
        for message in messages:
            with tempfile.TemporaryDirectory(prefix='evaluator-',dir=directory) as public:
                public=Path(public)
                (public/'message.bin').write_bytes(message)
                (public/'active.bin').write_bytes(select(inputs,message))
                r=guarded([executable,'evaluate',artifact_path,public/'message.bin',public/'active.bin',public/'output.bin'],public,native=True)
                peaks.append(r['peakMemoryBytes'])
                assert not r['stdout'] and not r['stderr'], 'unexpected evaluator side output'
                assert (public/'output.bin').read_bytes()==select(outputs,hash64(message)), 'wrong active output labels'
                cases+=1
        artifact_path.unlink()
    return {'artifactBytes':max(artifact_sizes),'measuredArtifactBytes':artifact_sizes,
            'activeLabelTrafficBytes':24576,'knownInputBytes':64,
            'totalIOBytes':max(artifact_sizes)+24640,
            'totalTransferredBytes':max(artifact_sizes)+24576,
            'labelEvaluationCases':cases,'runtimePeakMemoryBytes':max(peaks)}


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser()
    parser.add_argument('executable',type=Path)
    parser.add_argument('description',type=Path)
    parser.add_argument('directory',type=Path)
    parser.add_argument('result',type=Path)
    args=parser.parse_args()
    report=check_scheme(args.executable,json.loads(args.description.read_text()),args.directory)
    args.result.write_text(json.dumps(report,indent=2)+'\n')
    print(f"PASS: {report['labelEvaluationCases']} isolated scheme evaluations; all serialized bytes measured")
