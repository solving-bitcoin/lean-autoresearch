"""Independent Python byte vectors, cross-checked by Rust (not by Lean yet)."""
import argparse
import hashlib
import json
from pathlib import Path
from check_model import encode,MAXIMA,WEIGHTS

ROOT=Path(__file__).resolve().parents[1]
P=65537
H=lambda x:hashlib.sha256(x).digest()

def chain(node,n):
    for _ in range(n):node=H(node)
    return node

def vectors():
    seeds=[H(b'python-rust-vector-key'+bytes([j])) for j in range(67)]
    pk=b''.join(chain(seed,D) for seed,D in zip(seeds,MAXIMA))
    nonce=bytes(range(32));message=bytes(range(32));word=encode(message)
    sig=b''.join(chain(seed,d) for seed,d in zip(seeds,word))
    label=bytes((7*j+11)%256 for j in range(32))
    coins=bytes((17*j+3)%256 for j in range(16*1023*32))
    tables=[]
    for value in (False,True):
        i=37;j_target=2*(i//8)+(i%8<4)
        f=lambda d:((d>>(i%4))&1)==value
        points=[(j,k) for j,D in enumerate(MAXIMA) for k in range(D)
                for _ in range(WEIGHTS[j]+(int(f(k))-int(f(k+1)) if j==j_target else 0))]
        t=1023 if value else 1024
        polynomials=[]
        for limb in range(16):
            poly=[int.from_bytes(label[limb*2:limb*2+2],'little')]
            for degree in range(1,t):
                p=(limb*1023+degree-1)*32
                poly.append(int.from_bytes(coins[p:p+32],'little')%P)
            polynomials.append(poly)
        domain=lambda tag:tag+nonce+pk+i.to_bytes(2,'little')+bytes([value])
        rows=[]
        for index in (0,14,15,143,144,145,959,960,1000,len(points)-1):
            j,k=points[index];x=index+1
            plaintext=b''
            for poly in polynomials:
                acc=0
                for a in reversed(poly):acc=(acc*x+a)%P
                plaintext+=acc.to_bytes(3,'little')
            prefix=domain(b'WOTS-LAMPORT/mask/v1')+x.to_bytes(2,'little')+chain(seeds[j],k)
            mask=H(prefix+b'\0')+H(prefix+b'\1')[:16]
            rows.append({'index':index,'chain':j,'node':k,'ciphertext':bytes(a^b for a,b in zip(plaintext,mask)).hex()})
        tables.append({'wire':i,'value':value,'length':len(points)*48,
                       'commitment':H(domain(b'WOTS-LAMPORT/label/v1')+label).hex(),'rows':rows})
    return {'generator':'independent Python hashlib/integer implementation; fixtures only',
            'publicKeySha256':H(pk).hex(),'signatureSha256':H(sig).hex(),'word':word,'tables':tables}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    path=ROOT/'test-vectors.json';actual=vectors()
    if args.write:path.write_text(json.dumps(actual,indent=2)+'\n')
    else:assert json.loads(path.read_text())==actual
    print('PASS: Python public key/signature and 20 independent encrypted-share byte vectors')

if __name__=='__main__':main()
