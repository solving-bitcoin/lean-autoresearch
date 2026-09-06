"""Independent Python affine arithmetic checks the compiled Lean reference/I/O."""
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys

P = 21888242871839275222246405745257275088696311157297823662689037894645226208583
R = 21888242871839275222246405745257275088548364400416034343698204186575808495617
G = (1, 2)

def add(a, b):
    if a is None: return b
    if b is None: return a
    x,y = a; u,v = b
    if x == u and (y+v)%P == 0: return None
    m = ((3*x*x)*pow(2*y,-1,P) if a == b else (v-y)*pow(u-x,-1,P))%P
    z = (m*m-x-u)%P
    return z, (m*(x-z)-y)%P

def mul(n, a):
    acc = None
    while n:
        if n&1: acc=add(acc,a)
        a=add(a,a); n>>=1
    return acc

def le(n): return n.to_bytes(32,'little')
def affine(a): return le(a[0])+le(a[1])
def point(a): return bytes(65) if a is None else b'\1'+affine(a)
def private(q,r): return point(q)+le(r)

def cases():
    rng=random.Random(20260906)
    data=[(None,0,G),(None,1,G),(None,R-1,G),(G,0,G),(G,1,G),
          ((1,P-2),1,G),(None,0,mul(7,G)),(mul(12,G),R-1,mul(19,G))]
    for _ in range(12):
        a=mul(rng.randrange(1,R),G); r=rng.randrange(R)
        data.append((mul(rng.randrange(R),G),r,a))
    a=mul(333,G); r=123456789
    ra=mul(r,a); data.append(((ra[0],(-ra[1])%P),r,a))
    return data

def main():
    executable, runner, description, directory, result = map(Path,sys.argv[1:])
    metadata=json.loads(description.read_text())
    out=directory/'output.bin'
    def invoke(binary,args,ok=True):
        run=subprocess.run([str(binary),*map(str,args)],capture_output=True,timeout=30)
        if (run.returncode==0) != ok:
            raise AssertionError((args,run.returncode,run.stdout,run.stderr))
        return run
    def file(name,data):
        p=directory/name; p.write_bytes(data); return p
    samples=cases()
    for i,(q,r,a) in enumerate(samples):
        p=file('private.bin',private(q,r)); inp=file('input.bin',affine(a))
        invoke(executable,['reference',p,inp,out])
        assert out.read_bytes()==point(add(q,mul(r,a))), i
        for kind,raw in [('input',affine(a)),('private',private(q,r)),('output',point(add(q,mul(r,a))))]:
            src=file('codec.bin',raw);invoke(executable,['roundtrip',kind,src,out]);assert out.read_bytes()==raw
    invalid=[('input',le(P)+le(2)),('input',le(0)+le(0)),('input',le(1)+le(P)),
             ('input',affine(G)+b'\0'),('input',bytes(63)),
             ('output',b'\2'+affine(G)),('output',b'\0'+affine(G)),
             ('output',b'\1'+le(P)+le(2)),('output',bytes(64)),
             ('private',private(G,R)),('private',private(G,0)+b'\0'),
             ('private',b'\0'+affine(G)+le(0))]
    for kind,raw in invalid:
        invoke(executable,['roundtrip',kind,file('bad.bin',raw),out],ok=False)
    hash_vectors=[b'',b'abc',bytes(range(256)),b'x'*1024]+[b'x'*n for n in (55,56,63,64,65,127,128)]
    for raw in hash_vectors:
        invoke(executable,['sha256',file('hash.bin',raw),out]);assert out.read_bytes()==hashlib.sha256(raw).digest()
    runner_cases=0; sizes=[]
    if metadata['status'] in ('fixture','certified'):
        coins=file('coins.bin',bytes(metadata['randomnessBytes']))
        pairs_raw=b''.join(hashlib.sha256(b'g1-label'+i.to_bytes(4,'little')).digest() for i in range(1024))
        pairs=file('pairs.bin',pairs_raw); artifact=directory/'artifact.bin'
        for q,r,a in samples:
            raw=affine(a)
            active=b''.join(pairs_raw[32*(2*i+((raw[i//8]>>(i%8))&1)):32*(2*i+((raw[i//8]>>(i%8))&1)+1)] for i in range(512))
            run=invoke(runner,['garble',coins,file('private.bin',private(q,r)),pairs,artifact])
            size=artifact.stat().st_size
            assert json.loads(run.stdout)['artifactBytes']==size<=metadata['claimedBytes']
            sizes.append(size)
            invoke(runner,['evaluate',artifact,file('input.bin',raw),file('active.bin',active),out])
            assert out.read_bytes()==point(add(q,mul(r,a)));runner_cases+=1
            if metadata['status']=='fixture':
                assert artifact.read_bytes()==private(q,r)+pairs_raw+bytes(3)
                wrong=bytes([active[0]^1])+active[1:]
                invoke(runner,['evaluate',artifact,file('input.bin',raw),file('active.bin',wrong),out],ok=False)
        badpairs=file('pairs.bin',pairs_raw[:32]+pairs_raw[:32]+pairs_raw[64:])
        invoke(runner,['garble',coins,file('private.bin',private(G,1)),badpairs,artifact],ok=False)
        invoke(runner,['evaluate',artifact,file('input.bin',le(0)+le(0)),file('active.bin',bytes(16384)),out],ok=False)
        invoke(runner,['evaluate',artifact,file('input.bin',affine(G)),file('active.bin',bytes(16383)),out],ok=False)
    else:
        assert metadata == {'status':'unranked'}
        invoke(runner,['garble'],ok=False)
    report={'referenceCases':len(samples),'codecRoundtripCases':3*len(samples),
            'rejectedEncodings':len(invalid),'sha256Vectors':len(hash_vectors),'runnerCases':runner_cases,
            'observedArtifactBytes':max(sizes) if sizes else None}
    result.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report),flush=True)

if __name__ == '__main__': main()
