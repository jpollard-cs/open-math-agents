"""Enumerate actual cofactor LCMs, independently of prime compression."""
from math import lcm
from constructor import primes, audit

def cost(n):
    value=0
    q=2
    while q*q<=n:
        while n%q==0:
            n//=q
            value+=q-1
        q+=1
    return value+n-1

def brute(p,T):
    periods={1}
    for d in range(2,T+1):
        if d%p:
            periods.update([lcm(u,d) for u in periods])
    return min(cost(u) for u in periods if sum(u%d==0 for d in range(1,T+1))>=p)

count=0
for T in range(4,25):
    for p in primes(T-1):
        if p==2: continue
        c=brute(p,T)
        assert c==audit(p,T)[0],(p,T,c)
        count+=1
print(count,'cap/prime pairs independently optimized by complete cofactor-LCM enumeration')
for p,T in [(11,12),(11,16),(11,22),(11,44),(17,34),(31,62),(61,122),(101,202),(503,1006)]:
    c,qs,Q,M=audit(p,T)
    print(f'p={p} T={T} K={p+c} Q={Q} M={M}')
