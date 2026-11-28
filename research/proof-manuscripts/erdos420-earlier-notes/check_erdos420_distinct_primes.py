"""Finite consistency tests for the individual-window power-ratio lemma."""
from itertools import combinations
from math import comb,gcd,isqrt
from random import Random
from sympy import factorint, integer_nthroot, nextprime, primerange


def reduced_power_ratio(left,right,t):
    g=gcd(left,right)
    return integer_nthroot(left//g,t)[1] and integer_nthroot(right//g,t)[1]


def subset_signatures(n,h):
    # A rough part has no prime in common with any other row. Its largest
    # perfect-power exponent captures all divisibility tests on its valuations.
    factors=[]
    for i in range(1,h+1):
        value=n+i
        valuations={}
        for p in primerange(2,h+1):
            while value%p==0:
                valuations[p]=valuations.get(p,0)+1
                value//=p
        if value>1:
            valuations[-i]=max(t for t in range(1,value.bit_length()+1)
                               if integer_nthroot(value,t)[1])
        factors.append(valuations)
    tested=0
    for j in range(1,5):
        sets=list(combinations(range(h),j))
        signatures=[]
        for idx in sets:
            factors_of_product={}
            for i in idx:
                for p,e in factors[i].items():
                    factors_of_product[p]=factors_of_product.get(p,0)+e
            signatures.append(factors_of_product)
        for t in range(2,14):
            residues=[tuple(sorted((p,e%t) for p,e in f.items() if e%t)) for f in signatures]
            assert len(set(residues))==len(sets), (n,j,t)
            tested+=comb(len(sets),2)
    return tested


def check():
    rng=Random(420)
    starts=[10**13,10**16,10**20,10**24,10**30,10**32]
    # Include windows designed to have prescribed high-power rows.
    for t in (2,3,5,7,11,13):
        starts.append(210*int(nextprime(10000+t))**t-5)
    pairs=0
    spot=0
    for n in starts:
        pairs+=subset_signatures(n,10)
        for _ in range(60):
            j=rng.randrange(1,5)
            offsets=rng.sample(range(1,11),2*j)
            left=right=1
            for i in offsets[:j]:left*=n+i
            for i in offsets[j:]:right*=n+i
            assert not reduced_power_ratio(left,right,rng.choice([2,3,4,5,6,7,11,17,23,29,41]))
            spot+=1

    decompositions=0
    for y in range(2,151):
        # Obtain candidate products directly, independently of the greedy split in the proof.
        candidates={u*v for u in range(1,y+1) for v in range(u,y+1)}
        for d in range(1,isqrt(y**3)+1):
            if max(factorint(d),default=1)<=y:
                assert d in candidates
                decompositions+=1
    print(f"{pairs:,} same-cardinality subset-pair exponent tests on {len(starts)} individually specified starts.")
    print(f"{spot} independent gcd-and-integer-root spot checks, and {decompositions:,} smooth-part factorization checks.")
    print("All finite tests passed. The asymptotic statement is proved in the note.")
if __name__ == '__main__':
    check()
