"""Construct a prescribed-size example and verify its prime-digit certificate."""
from math import isqrt, lcm
from constructor import primes

def witness(k,p,T,other_primes=()):
    if p not in set(primes(p)) or T<p+1:
        raise ValueError("requires prime p and T>=p+1")
    ps=list(primes(p-1))
    D=[1]
    factors={}
    for q in ps:
        powers=[1,q]
        while (powers[-1]*q)**4<=T:
            powers.append(powers[-1]*q)
        factors[q]=len(powers)-1
        D=[d*v for d in D for v in powers if d*v<=T]
        if len(D)>=p:
            break
    if len(D)<p: raise ValueError("base period has too few cofactors")
    other_primes=tuple(other_primes)
    if (len(set(other_primes))!=len(other_primes) or
        any(q not in ps or q in factors for q in other_primes)):
        raise ValueError("prescribed primes must be distinct and above the base cutoff")
    r=k-p-sum((q-1)*a for q,a in factors.items())-sum(q-1 for q in other_primes)
    if r<0: raise ValueError("base period exceeds the cardinality budget")
    eligible=[q for q in ps if q not in other_primes and q**(factors.get(q,0)+1)<=T]
    prefix=[]
    capacity=0
    for q in eligible:
        if capacity>=r: break
        if q-1>capacity+1: raise ValueError("gap in optional costs")
        prefix.append(q)
        capacity+=q-1
    if capacity<r: raise ValueError("insufficient optional capacity")
    for q in reversed(prefix):
        if q-1<=r:
            r-=q-1
            factors[q]=factors.get(q,0)+1
    assert r==0
    factors.update((q,1) for q in other_primes)
    D=[1]
    rows=[]
    for q,a in sorted(factors.items()):
        ds=sorted(D)[:q-1]
        assert len(ds)==q-1 and ds[-1]*q**a<=p*T
        for j in range(1,a+1):
            for b,d in enumerate(ds,1):
                P=q**j
                rows.append((d*P,d*((pow(d,-1,P)*b*(P//q))%P)))
        D=[d*q**j for d in D for j in range(a+1) if d*q**j<=T]
    terminal=[q**a for q,a in factors.items()]
    Q=lcm(*terminal)
    ds=(terminal+[d for d in sorted(D) if d not in set(terminal)])[:p]
    assert len(ds)==p and lcm(*ds)==Q
    for b,d in enumerate(ds):
        rows.append((p*d,d*((b*pow(d,-1,p))%p)))
    moduli=[n for n,r in rows]
    assert len(set(moduli))==len(rows)==k and max(moduli)<=p*T
    assert lcm(*moduli)==p*Q
    assert all(1<n and 0<=r<n for n,r in rows)
    return rows

if __name__=='__main__':
    for k,p,T in [(1000,401,2493),(5000,2003,12481),(10000,4001,24993)]:
        rows=witness(k,p,T)
        print('size',k,'prescribed prime',p,'cap',p*T,'attained maximum',max(n for n,r in rows))
    for k,p,T,others in [(1000,307,3257,(281,)),(5000,1201,20815,(1151,1171))]:
        rows=witness(k,p,T,others)
        print('size',k,'simultaneous primes',others+(p,),'attained maximum',max(n for n,r in rows))
