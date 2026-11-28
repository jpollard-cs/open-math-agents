"""Construct the irreducible 64-row example and audit its full residue period."""
from collections import Counter
from itertools import combinations
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import json

def divisors(n):
    small = [i for i in range(1, isqrt(n) + 1) if n % i == 0]
    return sorted(set(small) | {n // i for i in small})

def crt(old, old_residue, new, new_residue):
    assert gcd(old, new) == 1
    return (old_residue + old * ((new_residue - old_residue) *
                                 pow(old, -1, new) % new)) % (old * new)

def witness():
    rows = []
    previous = 1
    for p,a in [(2,3),(3,2),(11,1),(13,1)]:
        factors = divisors(previous)
        assert len(factors) >= p - 1
        for j in range(1,a+1):
            for digit, e in enumerate(factors[:p-1], 1):
                b = p**j
                rows.append((e*b, crt(e,0,b,digit*p**(j-1)), b))
        previous *= p**a
    factors = divisors(previous)[:35]
    assert len(factors) == 35 and lcm(*factors) == previous
    for r,e in enumerate(factors):
        rows.append((35*e, crt(e,0,35,r), 35))
    return rows

def prime_powers(n):
    return [d for d in divisors(n) if d>1 and
            len([p for p in divisors(d) if p>1 and len(divisors(p))==2])==1]

def matching(A, labels):
    owners={b:[] for b in labels}
    def add(n,seen):
        for b in labels:
            if n % b or b in seen: continue
            seen.add(b)
            if len(owners[b]) < b:
                owners[b].append(n)
                return True
            for j,m in enumerate(owners[b]):
                if add(m,seen):
                    owners[b][j]=n
                    return True
        return False
    return sum(add(n,set()) for n in A)

def check():
    rows = witness()
    A=[d for d,r,b in rows]
    period=lcm(*A)
    assert len(set(A))==len(A)==64
    visited=[0]*period
    for d,r,b in rows:
        for t in range(r,period,d):
            visited[t]+=1
    assert min(visited)>0
    assert all(any(visited[t]==1 for t in range(r,period,d)) for d,r,b in rows)
    seen=Counter(b for d,r,b in rows)
    assert all(c<=b for b,c in seen.items())
    available=prime_powers(period)
    m=matching(A,available)
    assert sum(available)==62 and m<64
    assert matching(A,available+[35])==64
    print(f'{len(A)} distinct moduli, maximum {max(A)}, period {period}.')
    print(f'Every residue covered; all {len(A)} rows have private residues.')
    print(f'All prime-power slots total {sum(available)}; exact maximum placement {m}.')
    print('One permitted edge 5--7 places all 64 rows.')
    Path('example64.json').write_text(json.dumps(rows)+'\n')
if __name__=='__main__':
    check()
