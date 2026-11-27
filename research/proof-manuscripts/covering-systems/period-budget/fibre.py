"""Exact coverability on base period 72 times a single 5-digit.
Project the 5-fibres first; both projection and hole filling are exhaustive.
"""
from functools import cache,lru_cache

BASE = 72
ALL = (1<<BASE)-1

@cache
def masks(d):
    assert BASE % d == 0
    base=ALL//((1<<d)-1)
    return [base<<i for i in range(d)]

def partitions(values, k):
    groups=[]
    def assign(i):
        if i==len(values):
            if len(groups)==k: yield [tuple(g) for g in groups]
            return
        if k-len(groups)>len(values)-i: return
        d=values[i]
        for group in groups:
            group.append(d)
            yield from assign(i+1)
            group.pop()
        if len(groups)<k:
            groups.append([d])
            yield from assign(i+1)
            groups.pop()
    yield from assign(0)

def maxima(xs):
    answer=[]
    for x in sorted(set(xs),key=int.bit_count,reverse=True):
        if not any(x & y==x for y in answer):
            answer.append(x)
    return answer

@cache
def bucket(ds, allowed):
    values=[0]
    for d in ds: values=maxima(x | (y & allowed) for x in values for y in masks(d))
    return values

def canonical(x):
    return min(((x<<i)&ALL)|(x>>(BASE-i)) for i in range(BASE))

@cache
def permitted_holes(top):
    if len(top)<5: return (0,)
    assert len(top)<=9
    candidates={0}
    for groups in partitions(top,5):
        # At least one bucket has one modulus for all finite cases here.
        singleton=max(next(iter(g)) for g in groups if len(g)==1)
        groups.remove((singleton,))
        possible=[masks(singleton)[0]]
        for g in sorted(groups,key=lambda v:(len(v),-max(v))):
            possible=maxima(y for x in possible for y in bucket(g,x))
        candidates.update(canonical(x) for x in possible)
    return tuple(sorted(candidates,key=int.bit_count,reverse=True))

@lru_cache(maxsize=300000)
def fill(ds,holes):
    if holes==0:return True
    if not ds:return False
    gains=[max((holes&mask).bit_count() for mask in masks(d)) for d in ds]
    need=holes.bit_count()-sum(gains[1:])
    if need>gains[0]:return False
    ys=sorted({holes&mask for mask in masks(ds[0])},key=int.bit_count,reverse=True)
    return any(y.bit_count()>=need and fill(ds[1:],holes^y) for y in ys if y)

@cache
def base_decision(mods):
    # Mods may repeat following contraction.
    top=tuple(sorted(d//5 for d in mods if d%5==0))
    lower=tuple(sorted(d for d in mods if d%5))
    for h in permitted_holes(top):
        if fill(lower,ALL^h):return True
    return False
