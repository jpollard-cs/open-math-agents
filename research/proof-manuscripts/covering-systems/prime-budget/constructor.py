"""Optimize the number of prime digits needed for p cofactor slots below T."""
from math import gcd, lcm
from itertools import combinations
import argparse

def primes(n):
    flags = bytearray([1]) * (n+1)
    for i in range(2, n+1):
        if flags[i]:
            yield i
            flags[i*i:n+1:i] = bytes(len(range(i*i, n+1, i)))

def optimize(p,T):
    if p < 3 or p not in set(primes(p)) or T < p+1:
        raise ValueError("requires an odd prime p and T >= p+1")
    ps = [q for q in primes(T) if q != p]
    # A branch with no more exponents is always tested, including ties in cost.
    best = [sum((q-1)*maxexp(q,p+1) for q in ps if q<=p+1)+1, None]
    def visit(i, limit, cost, ds, profile):
        if len(ds)>=p:
            if cost<best[0]:
                best[:] = cost,profile
            return
        if i==len(ps): return
        q=ps[i]
        all_ds=list(ds)
        power=1
        for a in range(1,min(limit, maxexp(q,T))+1):
            power*=q
            c=cost+a*(q-1)
            if c>=best[0]: break
            all_ds.extend(d*power for d in ds if d*power<=T)
            visit(i+1,a,c,all_ds,profile+[(q,a)])
    visit(0,maxexp(2,T),0,[1],[])
    assert best[1] is not None
    return best

def maxexp(q,T):
    a=0
    while T>=q:
        a+=1
        T//=q
    return a

def realize(p,T,profile):
    old=1
    div=[1]
    rows=[]
    for q,a in profile:
        assert q<p
        cof=sorted(div)[:q-1]
        assert len(cof)==q-1
        for j in range(1,a+1):
            power=q**j
            for b,d in enumerate(cof,1):
                n=d*power
                residue=d*((pow(d,-1,power)*b*(power//q))%power)
                rows.append((n,residue))
        old*=q**a
        div=[d*q**j for d in div for j in range(a+1) if d*q**j<=T*p]
    mandatory=[q**a for q,a in profile]
    ds=mandatory+[d for d in sorted(div) if d<=T and d not in mandatory]
    ds=ds[:p]
    assert len(ds)==p and lcm(*ds)==old
    for b,d in enumerate(ds):
        rows.append((p*d,d*((b*pow(d,-1,p))%p)))
    assert len(set(n for n,r in rows))==len(rows) and max(n for n,r in rows)<=p*T
    return old,rows

def audit(p,T):
    cost,profile=optimize(p,T)
    Q,rows=realize(p,T,profile)
    assert len(rows)==p+cost
    if p*Q<=2_000_000:
        hit=bytearray(Q*p)
        lower=bytearray(Q)
        for n,r in rows:
            hit[r::n]=bytes([1])*len(hit[r::n])
            if n%p: lower[r::n]=bytes([1])*len(lower[r::n])
        assert all(hit) and sum(lower)==Q-1 and not lower[0]
    return cost,profile,Q,max(n for n,r in rows)

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('p',type=int)
    parser.add_argument('T',type=int)
    a=parser.parse_args()
    cost,profile,Q,M=audit(a.p,a.T)
    print('minimum cost',cost,'size',a.p+cost,'prime exponents',profile,'cofactor period',Q,'maximum modulus',M)
