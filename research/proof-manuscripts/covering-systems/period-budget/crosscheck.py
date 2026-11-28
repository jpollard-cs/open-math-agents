"""Independent exact solver. Split at the top ternary digit, anchor at a
private base point, then cover the remaining points directly on a 120-cycle.
"""
from functools import cache,lru_cache
from itertools import combinations, product
from math import lcm
import json
from pathlib import Path

L = 120
FULL = (1<<L)-1

@cache
def row(d):
    assert L % d == 0
    first = FULL//((1<<d)-1)
    return tuple(first<<r for r in range(d))

@lru_cache(maxsize=200000)
def fill(ds,holes):
    if holes==0: return True
    if not ds: return False
    caps=[max((holes&v).bit_count() for v in row(d)) for d in ds]
    required=holes.bit_count()-sum(caps[1:])
    if caps[0]<required: return False
    options=sorted({holes & v for v in row(ds[0])},key=int.bit_count,reverse=True)
    return any(fill(ds[1:],holes^gain) for gain in options if gain and gain.bit_count()>=required)

@cache
def all_base_masks(top):
    if len(top)<3:return (0,)
    out=set()
    # A nonempty lower-level hole can be translated to 0. At the three
    # lifts of zero choose different covering rows as anchors. Each anchor
    # has projected residue zero. Only one non-anchor row can be present.
    assert len(top)<=4
    for ids in combinations(range(len(top)),3):
        anchors=[row(top[i])[0] for i in ids]
        rem=[top[i] for i in range(len(top)) if i not in ids]
        if not rem:
            out.add(anchors[0]&anchors[1]&anchors[2]);continue
        for i in range(3):
            fixed=anchors[(i+1)%3]&anchors[(i+2)%3]
            for extra in row(rem[0]):
                out.add(fixed & (anchors[i]|extra))
    return tuple(sorted(out,key=int.bit_count,reverse=True))

@cache
def decide_base(ds):
    top=tuple(d//3 for d in ds if d%9==0)
    ds=tuple(d for d in ds if d%9)
    return any(fill(ds,FULL^allowed) for allowed in all_base_masks(top))

@cache
def decide(A):
    # Contract a full prime digit using only its input moduli; separated
    # from the production implementation so tuple order cannot leak across.
    ds=list(A)
    for p,high in ((7,7),(2,16)):
        top=[d for d in ds if d%high==0]
        if not top:continue
        assert len(top)<=p
        ds=[d for d in ds if d%high]
        if len(top)==p:ds.append(lcm(*(d//p for d in top)))
    return decide_base(tuple(sorted(ds)))

if __name__=='__main__':
    r=json.loads(Path('minima-through-56.json').read_text())
    # Independent lower bound for all forbidden sizes at caps <=55.
    pool=(2,3,4,5,6,8,9,10,12,15,16,18,20,24,30,36,40,45,48)
    for k in range(16,20):
        yes=[]
        for A in combinations(pool,k):
            if decide(A) and all(not decide(A[:i]+A[i+1:]) for i in range(k)):
                yes.append(A)
        assert len(yes)==int(k==16) and all(max(a)==48 for a in yes)
        print("cap 55, size",k,"irreducible sets",len(yes),flush=True)
    for x in r:
        A=tuple(x['example'])
        assert decide(A) and all(not decide(A[:i]+A[i+1:]) for i in range(len(A)))
        print("representative and all deletions verified:",x['max'],x['size'],flush=True)
