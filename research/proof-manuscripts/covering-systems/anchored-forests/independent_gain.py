"""Lower bound actual masses using integer interval arithmetic on harmonic prefixes."""
from bisect import bisect_left, bisect_right
from itertools import accumulate,combinations
from math import isqrt
from diamond_gain import select

def verify(groups):
    maximum=max(g[-1] for g in groups)*2
    box=10**24
    # Independent prime generator with trial division.
    primes=[]
    for n in range(2,maximum+1):
        limit=isqrt(n)
        for p in primes:
            if p>limit:
                primes.append(n)
                break
            if n%p==0:break
        else:primes.append(n)
    prime_mass=list(accumulate((box//p for p in primes),initial=0))
    integer_mass=list(accumulate((box//n for n in range(1,maximum+1)),initial=0))
    total=0
    used=set()
    for group in groups:
        a=group[0]
        j=bisect_left(primes,a)
        assert primes[j:j+4]==group and not used.intersection(group)
        used.update(group)
        for p in group:
            lo,hi=1,2*a-1
            while lo<hi:
                mid=(lo+hi)//2
                if mid-(bisect_right(primes,mid)-j if mid>=a else 0) >= p-2:hi=mid
                else:lo=mid+1
            end=lo; jj=max(j,bisect_right(primes,end))
            assert end-(jj-j)==p-2 and end<2*a
            selected=integer_mass[end]-(prime_mass[jj]-prime_mass[j])
            old_upper=integer_mass[p-1]+p-1
            total+=(selected-old_upper)//p
        for p,q in list(combinations(group,2))[:-1]:
            total+=box//(p*q)
    return total,box

if __name__=='__main__':
    fixed,groups=select(100000)
    lower,scale=verify(groups)
    assert lower*10**12 >= fixed*scale
    print('independent lower bound',lower,'/',scale,'using',len(groups),'disjoint quartets')
