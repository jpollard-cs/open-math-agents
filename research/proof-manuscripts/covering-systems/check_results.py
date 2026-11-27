"""Check witnesses, global bounds, binary-tree coverage, and counts in an external data file."""
from collections import Counter
from fractions import Fraction
from itertools import combinations
from math import comb, lcm
from pathlib import Path
from sys import argv

from cover_search import irreducible
from seed_certificates import SEEDS
from spectrum import construct, fixed_size, normalized, prime_factors


def formula_sets(a,q):
    for n in range(q-1,a+1):
        for W in combinations(range(a),n):
            reserve=max(W[:q-1])
            yield tuple(sorted([q << i for i in (*W,a)] +
                              [1 << i for i in range(1,a+1) if i<=reserve or i not in W]))


def check():
    for s in SEEDS.values(): assert irreducible(s)
    print("Both seeds cover; re-optimizing binary and odd residues after each single deletion always fails.")
    tested=checked_periods=0
    for u in range(1,80,2):
        fs=prime_factors(u)
        for d in range(8):
            C=construct(u,d)
            if u==1 or (len(fs)==1 and d==1):
                assert C is None
                continue
            target=Fraction(u,1 << (sum(p-1 for p in fs)+d))
            assert normalized(C)==target
            N=lcm(*C)
            if N<=180000:
                flags=bytearray(N)
                for m,r in C.items():
                    flags[r::m]=bytes([1])*(N//m)
                assert all(flags)
                checked_periods+=1
            tested+=1
    print(tested,"symbolic sets constructed with exact ratio;",checked_periods,"entire periods exhaustively checked.")
    for q in (3,5,7):
        for a in range(1,11):
            count=len(set(formula_sets(a,q)))
            assert count==sum(comb(a,j) for j in range(q-1,a+1))
    # Above 1/8 only 3 and 5 can occur, with the stated exponent cutoffs.
    leaders=[]
    for e in range(8):
        for h in range(2):
            u=3**e*5**h
            for d in range(4):
                target=Fraction(u,2**(2*e+4*h+d))
                if u==1 or (e+h==1 and d==1) or target<Fraction(1,8):continue
                cover=construct(u,d)
                assert normalized(cover)==target and len(cover)<=17
                leaders.append(target)
    assert len(leaders)==16
    print("Top 16 for all k >= 17:",', '.join(map(str,sorted(leaders,reverse=True))))
    for k in range(5,31):
        for u in range(1,80,2):
            for a in range(k):
                m=u<<a
                if 9*m*m>4*3**k:
                    status,_=fixed_size(k,m)
                    assert status in ("attainable","impossible")
    print("Upper-range constructor checked through k=30, all odd parts through 79.")
    if len(argv)>1:
        from ast import literal_eval
        rows={tuple(literal_eval(x.split(']')[0]+']')) for x in Path(argv[1]).read_text().splitlines() if x.startswith('[')}
        all_rows=set()
        for row in rows:
            while len(row)<=10:
                all_rows.add(row)
                row=(2,)+tuple(2*x for x in row)
        for k in range(5,11):
            actual={r for r in all_rows if len(r)==k and max(r)==3*2**(k-3)}
            assert actual==set(formula_sets(k-3,3))
            observed={max(r) for r in all_rows if len(r)==k and 9*max(r)**2>4*3**k}
            predicted={m for m in range(2,3*(1<<(k-3))+1) if 9*m*m>4*3**k and fixed_size(k,m)[0]=='attainable'}
            assert predicted==observed
            print("External data, size",k,":",len(actual),"exact peak sets, identical to generated sets.")
if __name__=='__main__':check()
