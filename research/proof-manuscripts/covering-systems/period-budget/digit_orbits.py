"""Represent assignments of residues up to relabeling each prime-power digit.

At each parent prefix of a prime-power digit, name the children in the order
in which the rows first visit them. The direct product of these permutations
preserves every congruence modulus and covers the whole symmetry used here.
"""
from functools import cache
from itertools import product

@cache
def paths(d):
    fs=[]
    for p in (2,3,5,7):
        v=1
        while d%(p*v)==0:
            fs.append((p,v));v*=p
    return tuple(tuple(((p,r%v,v),r//v%p) for p,v in fs) for r in range(d))

def orbits(ds):
    def recur(i,known,rr):
        if i==len(ds):
            yield rr;return
        for r,path in enumerate(paths(ds[i])):
            if all(val<=known.get(node,0) for node,val in path):
                nxt=dict(known)
                for node,val in path:
                    nxt[node]=max(nxt.get(node,0),val+1)
                yield from recur(i+1,nxt,rr+(r,))
    yield from recur(0,{},())

@cache
def blocks(ds,prime,base):
    from math import prod
    # ds are original moduli, with all highest p-adic powers equal
    high=1
    if ds:
        while ds[0]%(prime*high)==0:high*=prime
    ans=set()
    for rr in orbits(ds):
        parts=[0]*prime
        for d,r in zip(ds,rr):
            quo=d//prime
            reg=((1<<base)-1)//((1<<quo)-1)
            parts[(r%high)//(high//prime)] |= reg<<(r%quo)
        ans.add(tuple(parts))
    return tuple(ans)
