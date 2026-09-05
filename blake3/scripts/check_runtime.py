"""Native end-to-end and hostile framing tests for the protected backend."""
import argparse
import hashlib
import json
from pathlib import Path
import secrets
import subprocess
import sys
import tempfile
import time

from garble import Circuit, FIXED_BYTES, garble, evaluate, fresh_pairs, select_input, select_output
from reference import hash64


def expect_error(action):
    try:
        action()
    except (ValueError, TypeError, KeyError):
        return
    raise AssertionError('malformed input was accepted')


def check_kernel():
    # XOR, AND, complemented wires, constants, and duplicate inputs.
    gates = ((False,2,4), (True,2,4), (True,3,4), (False,3,5),
             (True,1,2), (True,0,4), (True,2,2), (True,2,3))
    pattern = tuple(2*(513+i) for i in range(8)) + (0,1,2,3)
    outputs = (pattern*22)[:256]
    c = Circuit(gates, outputs, FIXED_BYTES + 6*64)
    ip, op = fresh_pairs(512), fresh_pairs(256)
    # Includes boundary selector indices 0 and 255, and pairs whose low bits agree.
    ip[0] = (bytes(32), (1 << 255).to_bytes(32,'little'))
    ip[1] = (bytes(32), (1).to_bytes(32,'little'))
    artifact = garble(c,ip,op)
    for a in range(2):
        for b in range(2):
            message = bytes([a+2*b])+bytes(63)
            assert evaluate(c,artifact,select_input(ip,message)) == select_output(op,c.plain(message))
    expect_error(lambda: evaluate(c, artifact[:-1], select_input(ip, bytes(64))))
    expect_error(lambda: evaluate(c, artifact+b'\0', select_input(ip, bytes(64))))
    expect_error(lambda: evaluate(c, artifact, [bytes(31)]*512))
    expect_error(lambda: evaluate(c, artifact, [bytes(32)]*511))
    bad = list(ip); bad[0] = (bytes(32),bytes(32))
    expect_error(lambda: garble(c,bad,op))
    print('PASS: half-gate truth tables, XOR/complements, constants, arbitrary selectors, framing')


def worker(circuit_path: Path, artifact_path: Path, labels_path: Path, output_path: Path):
    circuit = Circuit.from_json(json.loads(circuit_path.read_text()))
    labels = labels_path.read_bytes()
    if len(labels) != 512*32:
        raise ValueError('wrong active-label channel length')
    result = evaluate(circuit,artifact_path.read_bytes(),tuple(labels[i:i+32] for i in range(0,len(labels),32)))
    output_path.write_bytes(b''.join(result))


def main():
    if len(sys.argv)>1 and sys.argv[1]=='worker':
        worker(*(Path(p) for p in sys.argv[2:]))
        return
    p=argparse.ArgumentParser()
    p.add_argument('circuit',type=Path)
    p.add_argument('--result',type=Path,required=True)
    args=p.parse_args()
    check_kernel()
    raw = json.loads(args.circuit.read_text())
    circuit = Circuit.from_json(raw)
    vector = json.loads((Path(__file__).resolve().parents[1]/'tests/official-vector.json').read_text())
    assert hash64(bytes.fromhex(vector['inputHex'])).hex() == vector['digestHex']
    fixed = [bytes(64),bytes([255])*64,bytes(range(64)),bytes([0x55,0xaa])*32]
    flips = [(1<<i).to_bytes(64,'little') for i in range(512)]
    for msg in fixed+flips+[secrets.token_bytes(64) for _ in range(16)]:
        assert circuit.plain(msg)==hash64(msg), 'circuit/reference mismatch'
    print('PASS: official BLAKE3 vector, all 512 single-bit inputs, 16 random inputs, fixed patterns')
    ip,op = fresh_pairs(512),fresh_pairs(256)
    start=time.monotonic(); artifact=garble(circuit,ip,op); garble_ms=1000*(time.monotonic()-start)
    assert len(artifact)==circuit.artifact_bytes <= circuit.claimed_bytes
    eval_ms=[]
    for msg in fixed+[secrets.token_bytes(64) for _ in range(4)]:
        active=select_input(ip,msg)
        start=time.monotonic();result=evaluate(circuit,artifact,active);eval_ms.append(1000*(time.monotonic()-start))
        assert result==select_output(op,hash64(msg)), 'wrong output labels'
    second=garble(circuit,ip,op)
    assert second!=artifact, 'fresh garbling randomness did not change the artifact'
    msg=secrets.token_bytes(64)
    assert evaluate(circuit,second,select_input(ip,msg))==select_output(op,hash64(msg))
    with tempfile.TemporaryDirectory(prefix='blake3-label-worker-') as td:
        td=Path(td)
        (td/'artifact').write_bytes(artifact)
        (td/'labels').write_bytes(b''.join(select_input(ip,msg)))
        subprocess.run([sys.executable,str(Path(__file__).resolve()),'worker',str(args.circuit.resolve()),
                        str(td/'artifact'),str(td/'labels'),str(td/'output')],check=True,timeout=60)
        assert (td/'output').read_bytes()==b''.join(select_output(op,hash64(msg)))
    for length in (0,63,65):
        expect_error(lambda length=length: hash64(bytes(length)))
    for field in ('inputBits','outputBits','schemaVersion'):
        invalid=dict(raw);invalid[field]=0
        expect_error(lambda invalid=invalid: Circuit.from_json(invalid))
    invalid=dict(raw);invalid['outputs']=[10**9]*256
    expect_error(lambda: Circuit.from_json(invalid))
    invalid=dict(raw);invalid['claimedBytes']=0
    expect_error(lambda: Circuit.from_json(invalid))
    print('PASS: reused artifact on eight inputs, fresh randomness, and separate-process evaluation')
    report={'challenge':'blake3-64-labeled-hash','correct':True,
            'artifactBytes':len(artifact),'claimedBytes':circuit.claimed_bytes,
            'andGates':circuit.and_count,'xorGates':len(circuit.gates)-circuit.and_count,
            'inputAdapterBytes':512*65,'outputAdapterBytes':256*64,'constantLabelBytes':32,
            'andTableBytes':circuit.and_count*64,'activeInputLabelBytes':512*32,
            'activeOutputLabelBytes':256*32,'totalTransferredBytes':len(artifact)+768*32,
            'garbleMilliseconds':round(garble_ms,2),'meanEvaluateMilliseconds':round(sum(eval_ms)/len(eval_ms),2),
            'artifactDigest':hashlib.sha256(artifact).hexdigest()}
    args.result.parent.mkdir(parents=True,exist_ok=True)
    args.result.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))

if __name__=='__main__':main()
