"""Exact bookkeeping checks, NOT a security reduction or probabilistic proof."""
from fractions import Fraction
import json
from pathlib import Path
from check_model import MAXIMA,WEIGHTS

ROOT=Path(__file__).resolve().parents[1]

def main():
    p=65537
    blocks=512*16*1023
    used=256*16*(1023+1022)
    assert blocks==8380416 and used==8376320
    assert 32+blocks*32==268173344
    # Coin intervals used by each independent limb/polynomial are disjoint.
    # This checks ALL 8,192 ranges without allocating millions of integers.
    previous=32
    used_bytes=0
    for wire in range(256):
        for value in (0,1):
            degree=1023-value
            for limb in range(16):
                start=32+((2*wire+value)*16+limb)*1023*32
                end=start+degree*32
                assert previous<=start<end<=268173344
                used_bytes+=end-start
                previous=end
    assert used_bytes==used*32
    assert 268173344-32-used_bytes==4096*32
    # Modulo sampling: one exceptional residue, the others have equal mass.
    N=2**256
    quotient,remainder=divmod(N,p)
    assert remainder==1
    exact_tv=Fraction(1,2)*(abs(Fraction(quotient+1,N)-Fraction(1,p))+
                            (p-1)*abs(Fraction(quotient,N)-Fraction(1,p)))
    assert exact_tv==Fraction(p-1,p*N)
    assert used*exact_tv < Fraction(1,2**233)
    # All possible 16-bit limb values embed injectively; the field has one
    # additional value which must be rejected at final label decoding.
    assert len({i%p for i in range(65536)})==65536
    assert all(pow(i,p-2,p)*i%p==1 for i in range(1,p))
    # Count primitive hash calls in the current straightforward LEAN source.
    # Across both predicates f0+f1=1, so signed multiplicity corrections cancel.
    endpoint_queries=sum(MAXIMA)
    evaluations=512*sum(w*D for w,D in zip(WEIGHTS,MAXIMA))
    node_queries=512*sum(w*D*(D-1)//2 for w,D in zip(WEIGHTS,MAXIMA))
    prepare_queries=2*endpoint_queries+512+2*evaluations+node_queries
    evaluate_queries_upper=endpoint_queries+256*1024*(14+2)+256
    assert endpoint_queries==989
    assert evaluations==1015296
    assert prepare_queries==9011130
    assert evaluate_queries_upper==4195549
    honest_upper=prepare_queries+endpoint_queries+evaluate_queries_upper
    assert honest_upper==13207668 and honest_upper<2**32
    # Nontrivial rational target and bias headroom are necessary bookkeeping,
    # not evidence that the joint ROM loss is bounded by this expression.
    error=lambda q:Fraction(2**20*(q+2**32+1)**2,2**256)
    assert used*exact_tv < error(0) < error(2**48) < 1
    config=json.loads((ROOT/'challenge.json').read_text())
    assert config['profile']['maxAdversaryQueries']==2**48
    assert config['profile']['honestQueryBudget']==2**32
    print('PASS: 8,192 disjoint coefficient ranges; 8,376,320 used blocks; joint sampler-distance upper bound < 2^-233')
    print('PASS: all 65,536 nonzero inverses; lossless 16-bit limbs; one excluded field residue')
    print(f'PASS: symbolic hash-call ledger: Prepare={prepare_queries}, Sign<={endpoint_queries}, Expand<={evaluate_queries_upper}, total<={honest_upper}<2^32')
    print('NOT PROVED: the loop-count connection in Lean or any joint cryptographic ROM bound')

if __name__=='__main__':main()
