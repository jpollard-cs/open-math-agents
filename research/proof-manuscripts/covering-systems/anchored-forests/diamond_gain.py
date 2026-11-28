"""Exact reciprocal gain certificates for disjoint binary diamonds on consecutive primes."""
from fractions import Fraction as F
from itertools import combinations
from math import isqrt

def primes(n):
    table = bytearray(b'\1') * (n+1)
    table[:2] = b'\0\0'
    for p in range(2,isqrt(n)+1):
        if table[p]:
            table[p*p::p] = b'\0'*((n-p*p)//p+1)
    return [p for p in range(2,n+1) if table[p]]

def quartet(ps, prime_set):
    first = ps[0]
    total = sum(F(1,p*q) for p,q in combinations(ps,2) if (p,q)!=tuple(ps[2:]))
    replacements = []
    for j,p in enumerate(ps):
        missing = list(ps[:j]) if j else [p-1]
        added = []
        candidate = p
        while len(added) < len(missing)-1:
            if candidate not in prime_set:
                added.append(candidate)
            candidate += 1
        assert candidate <= 2*first and p <= 2*first
        total += sum(F(1,p*x) for x in added) - sum(F(1,p*x) for x in missing)
        replacements.append((missing,added))
    return total,replacements

def select(limit):
    prime_table = primes(limit+100)
    prime_set = set(prime_table)
    ps = [p for p in prime_table if 29<=p<=limit]
    # Lower round every gain to 10^-12 before optimizing. All arithmetic is integral.
    units=10**12
    best=[0]*(len(ps)+1)
    take=[False]*len(best)
    for i in range(1,len(best)):
        best[i] = best[i-1]
        if i >= 4:
            g,_ = quartet(ps[i-4:i],prime_set)
            candidate = best[i-4]+int(g*units//1)
            if candidate > best[i]:
                best[i] = candidate
                take[i] = True
    groups=[]
    i=len(ps)
    while i:
        if take[i]:
            groups.append(ps[i-4:i]); i-=4
        else: i-=1
    return best[-1],groups[::-1]

if __name__=='__main__':
    ps=[37,41,43,47]
    print('First example:',ps,quartet(ps,set(primes(200))))
    for n in (100,300,1000,10000,100000):
        floor,groups=select(n)
        print(n,len(groups),floor,'units of 10^-12', 'first groups',groups[:4])
