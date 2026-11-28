"""Exact rational checks of the ordinary chords on both EHPS sheets."""
from fractions import Fraction as F
from random import Random
from block_moments import moments,polygons

def inside(s,t,high,e):
    a,b=t+F(1,2), s-t-F(1,2)
    if not (F(1,2)<a<1 and 0<b<1):
        return False
    if high:
        return b<F(1,2) and F(7,6)+e<s<F(17,12)
    return F(2,3)<s<F(7,6)

def verify(m, high_count, narrow, rng):
    e=F(7,48*m)
    eta2=3*e*e/13
    high=[i<high_count for i in range(m)]
    s0=[F(137,100) if h else F(71,100) for h in high]
    t0=[F(46,100) if h else F(9,100) for h in high]
    # Match the weighted signed sum in pairs within each patch.
    signs=[1 if (i if h else i-high_count)%2==0 else -1 for i,h in enumerate(high)]
    u=[sign*(1+F(rng.randrange(10),10000)) for sign in signs]
    v=[F(rng.randrange(-20,21),20) / (1 if narrow else e) for _ in high]
    correction=-sum(s*a+eta2*t*b for s,t,a,b in zip(s0,t0,u,v))/sum(map(abs,u))
    scale=1+F(rng.randrange(-3,4),5000)
    center=[(scale*(s+correction*sign),scale*t) for s,t,sign in zip(s0,t0,signs)]
    assert sum(s*a+eta2*t*b for (s,t),a,b in zip(center,u,v))==0
    factor=F(1,200)*(1 if narrow else e)
    E=lambda s,t:s*s+eta2*t*t
    total=[F(0)]*3
    for (s,t),a,b,h in zip(center,u,v,high):
        for j,k in enumerate([-1,0,1]):
            S,T=s+k*factor*a,t+k*factor*b
            assert inside(S,T,h,e)
            total[j]+=E(S,T)
    assert total[0]==total[2] and total[0]-total[1]==factor**2*sum(E(a,b) for a,b in zip(u,v))
    return 1

if __name__=='__main__':
    a,v=zip(*(moments(p) for p in polygons()))
    assert sum(a)==F(7,24) and sum(v)/sum(a)==F(3515,3024)
    rng=Random(142)
    n=sum(verify(m,k,narrow,rng) for m in (8,16,32,64) for k in range(0,m+1,2)
          for narrow in (False,True) for _ in range(4))
    print(f"{n} rational chords verified. Limiting mean squared sum = {sum(v)/sum(a)}.")
