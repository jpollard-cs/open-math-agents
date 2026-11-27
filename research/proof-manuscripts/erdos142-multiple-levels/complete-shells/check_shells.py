"""Construct witnesses and exhaust small cubes using ordinary integer arithmetic."""
from itertools import product
from math import isqrt
from random import Random
from collections import Counter

def four_squares(n):
    if not n:
        return [0]*4
    scale=1
    while n%4==0:
        n//=4
        scale*=2
    first=int(n%8==7)
    rem=n-first
    for a in range(isqrt(rem),-1,-1):
        target=rem-a*a
        if target%4==3: continue
        for b in range(isqrt(target),-1,-1):
            c=isqrt(target-b*b)
            if b*b+c*c==target:
                return [scale*i for i in (first,a,b,c)]
    raise AssertionError("four squares")

def check(x,y,z,q,r,g,d):
    sq=lambda v:sum(s*s for s in v)
    assert len(x)==len(y)==len(z)==d
    assert all(0<=a<=q and 0<=b<=q and 0<=c<=q and a+c==2*b for a,b,c in zip(x,y,z))
    assert sq(y)==r and sq(x)==sq(z)==r+g and x!=z

def bulk(q,d,r,g):
    assert g>=2 and r>=g+3 and d*q*q-r>=9*g+15*q*q
    X=[]; V=[]
    if g%2:
        assert q>=3
        X.extend((1,1,2)); V.extend((1,1,-1))
    z=(g-3*(g%2))//2
    w=q//2
    count,left=divmod(z,w*w)
    for t in [w]*count+four_squares(left):
        X.extend((t,t)); V.extend((t,-t))
    rem=r-sum(i*i for i in X)
    count,left=divmod(rem,q*q)
    filler=[q]*count+four_squares(left)
    X.extend(filler); V.extend([0]*len(filler))
    assert len(X)<=d
    X.extend([0]*(d-len(X))); V.extend([0]*(d-len(V)))
    check([a-v for a,v in zip(X,V)],X,[a+v for a,v in zip(X,V)],q,r,g,d)

def high_fill(q,D):
    assert q>=2**24 and D*D>=100**2*q**3 and 0<D<=64*q*q
    sat=max(0,(D-1)//(q*q)-1)
    rem=D-sat*q*q
    digits=[0]*sat
    if rem%2:
        digits.append(q-1)
        rem-=2*q-1
    assert 0<rem<=2*q*q
    lo,hi=0,q//2
    while lo<hi:
        a=(lo+hi)//2
        if 8*(2*q*a-a*a)>=rem: hi=a
        else: lo=a+1
    a=lo
    k=(8*(2*q*a-a*a)-rem)//2
    assert 0<=k<=a*a
    for v in four_squares(k):
        digits.extend((q-a-v,q-a+v))
    assert all(0<=i<=q for i in digits)
    assert sum(q*q-i*i for i in digits)==D
    return digits

def top(q,d,D,g):
    assert g%2==0 and 2<=g and 1024*g<=q*q and 1024*g*q*q<=D*D
    ys=[]; vs=[]
    for t in four_squares(g//2):
        ys.extend((q-t,q-t));vs.extend((t,-t))
    Drem=D-sum(q*q-y*y for y in ys)
    filler=high_fill(q,Drem)
    ys.extend(filler); vs.extend([0]*len(filler))
    assert len(ys)<=d
    ys.extend([q]*(d-len(ys)));vs.extend([0]*(d-len(vs)))
    check([y-v for y,v in zip(ys,vs)],ys,[y+v for y,v in zip(ys,vs)],q,d*q*q-D,g,d)

def verify_small(q,d):
    local=[(a,(a+c)//2,c) for a in range(q+1) for c in range(q+1) if (a+c)%2==0]
    n=0
    for triple in product(local,repeat=d):
        if all(a==c for a,b,c in triple):continue
        x,y,z=(sum(v*v for v in coord) for coord in zip(*triple))
        assert max(x,y,z)-min(x,y,z)>=2
        if q==2 and len({x,y,z})<=2:
            assert (max(x,y,z)-min(x,y,z))%2==0
        n+=1
    return n

if __name__=='__main__':
    rng=Random(142)
    print('Nonconstant ordered triples checked in small cubes:')
    for q,d in ((2,8),(3,6),(4,4),(5,4)):
        print(q,d,verify_small(q,d))
    for _ in range(400):
        q=rng.randrange(3,1000);d=rng.randrange(180,500)
        r=rng.randrange(d*q*q//4,d*q*q//2)
        g=rng.randrange(2,min(r-2,(d*q*q-r-15*q*q)//9))
        bulk(q,d,r,g)
    for q in (2**24,2**24+1,2**25+3):
        for mult in (1,2,20,60):
            D=mult*q*q-301
            for gap in (2,154,100004,10000004):
                top(q,120,D,gap)
    counts=Counter({0:1})
    for _ in range(12):
        nxt=Counter()
        for s,c in counts.items():
            for j in range(4):nxt[s+j*j]+=c
        counts=nxt
    v,r=max((counts[r]+counts[r+1],r) for r in range(109))
    print('400 bulk and 48 near-corner witness triples passed.')
    print('q=3, d=12: best adjacent pair starts at',r,'and has',v,'points.')
    assert (v,r)==(1138038,41)
