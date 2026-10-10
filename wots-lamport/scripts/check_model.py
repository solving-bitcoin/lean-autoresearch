"""Independent integer checks; no result in this script is a Lean certificate."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MAXIMA = [15]*64 + [7,7,15]
WEIGHTS = [1]*64 + [1,8,64]

def encode(message):
    assert len(message) == 32
    digits = [digit for b in message for digit in (b//16,b%16)]
    c = sum(15-d for d in digits)
    return digits + [c%8,(c//8)%8,c//64]

def decode(word):
    if len(word)!=67 or any(not 0<=d<=D for d,D in zip(word,MAXIMA)):
        return None
    message=bytes(16*word[2*i]+word[2*i+1] for i in range(32))
    return message if encode(message)==word else None

def message_for_sum(total):
    d=[]
    for _ in range(64):
        digit=min(15,total);d.append(digit);total-=digit
    assert total==0
    return bytes(16*d[2*i]+d[2*i+1] for i in range(32))

def main():
    assert sum(D*w for D,w in zip(MAXIMA,WEIGHTS)) == 1983
    cases=0
    for total in range(961):
        message=message_for_sum(total);word=encode(message)
        assert decode(word)==message
        assert sum(d*w for d,w in zip(word,WEIGHTS))==960
        assert sum((D-d)*w for d,D,w in zip(word,MAXIMA,WEIGHTS))==1023
        for i in range(256):
            j=2*(i//8)+(1 if i%8<4 else 0)
            assert (word[j]>>(i%4))&1 == (message[i//8]>>(i%8))&1
        cases+=1
    # Every Boolean predicate on a small coordinate, every start, both weighted
    # and ordinary specializations: integer multiplicities and telescoping.
    helper=0
    for D in range(1,8):
        for truth in range(1<<(D+1)):
            f=lambda k:(truth>>k)&1
            for w in (1,8,64):
                h=[w+f(k)-f(k+1) for k in range(D)]
                assert all(0<=v<=w+1 for v in h)
                for c in range(D+1):
                    assert sum(h[c:]) == w*(D-c)+f(c)-f(D)
                    helper+=1
    # Selected geometry admits no componentwise domination between DIFFERENT
    # valid words: positive weights and a fixed weighted sum suffice.
    words=[encode(message_for_sum(i)) for i in range(961)]
    for a,b in zip(words,words[1:]):
        assert not all(x<=y for x,y in zip(a,b))
        assert not all(y<=x for x,y in zip(a,b))
    assert decode([0]*67) is None
    assert decode([16]*67) is None
    assert 65537>1984 and all(65537%d for d in range(2,257))
    assert pow(2,256,65537)==1  # biased coefficient sampler: NOT exactly uniform
    c=json.loads((ROOT/'challenge.json').read_text())
    assert c['scoring']['claimBytes']==2144+32+512*32+256*3966*48
    assert c['scoring']['randomnessBytes']==32+512*16*1023*32
    assert c['scoring']['score'] is None
    print(f'PASS: {cases} checksum totals, 246016 bit mappings, {helper} weighted telescoping cases, 1920 adjacent antichain comparisons')
    print('PASS: prime/point capacity, coefficient bias identity, exact layout arithmetic (not universal Lean proofs)')

if __name__=='__main__': main()
