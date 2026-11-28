"""Two independent finite counts for the switching step of Conjecture 4.4."""
from functools import cache
from itertools import product
from math import gcd,lcm,prod
from fractions import Fraction as Q
from random import Random
def divisors(m):
    return [d for d in range(2,m+1) if m%d==0]
@cache
def opt(m):
    states={0}
    for d in divisors(m):
        classes=[sum(1<<x for x in range(a,m,d)) for a in range(d)]
        states={mask|c for mask in states for c in classes}
    return max(s.bit_count() for s in states)
def test(m,n,labels):
    dm=divisors(m);dn=divisors(n)
    assert gcd(m,n)==1
    A={x for x in range(m) if any(x%d==labels[d] for d in dm)}
    B={y for y in range(n) if any(y%e==labels[e] for e in dn)}
    lhs=sum(any(x%d==a for d,a in labels.items()) for x in range(m*n))
    counted=ownerloss=discard=0
    for y in range(n):
        if y in B:counted+=m;continue
        chosen={};original=set(A)
        for d in dm:
            active=[labels[d*e]%d for e in dn if y%e==labels[d*e]%e]
            chosen[d]=active[0] if active else labels[d]
            for a in active:original.update(range(a,m,d))
            discard+=len(active[1:])*(m//d)
        kept={x for x in range(m) if any(x%d==a for d,a in chosen.items())}
        assert len(kept)<=opt(m)
        for x in A:
            d=next(d for d in dm if x%d==labels[d])
            ownerloss+=int(chosen[d]!=labels[d])
        counted+=len(original)
    assert counted==lhs
    assert ownerloss<=len(A)*opt(n)
    pairs=sum((Q(1,lcm(e,f)) for e in dn for f in dn if e<f),Q())
    sm=sum((Q(1,d) for d in dm),Q());sn=sum((Q(1,e) for e in dn),Q())
    assert discard<=m*n*sm*pairs
    assert lhs<=m*len(B)+(n-len(B))*opt(m)+ownerloss+discard
    assert 2*pairs<=(3+sn)*sn*sn
    assert lhs+m*n<=(m+opt(m))*(n+opt(n))
if __name__=='__main__':
    all_tests=random_tests=0
    for m,n in [(2,3),(3,2),(2,5),(3,4),(4,3),(2,9)]:
        ds=divisors(m*n)
        for labels in product(*(range(d) for d in ds)):
            test(m,n,dict(zip(ds,labels)));all_tests+=1
    rng=Random(20261128)
    for m,n in [(8,9),(9,8),(10,9),(6,7),(12,5),(4,15)]:
        for i in range(150):
            test(m,n,{d:rng.randrange(d) for d in divisors(m*n)});random_tests+=1
    print(all_tests,'exhaustive labelled assignments;',random_tests,'additional assignments')
