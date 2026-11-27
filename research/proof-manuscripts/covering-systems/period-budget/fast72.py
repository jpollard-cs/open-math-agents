"""Three-digit projection using canonical residue trees at cap 72."""
from functools import cache
from mixed70 import all7, canon
from digit_orbits import blocks
from crosscheck import fill, FULL

def high_three_options(ds):
    return blocks(tuple(3*d for d in ds),3,120)

@cache
def allowance(seven,three):
    a7=all7(seven)
    s=set()
    for u,v,w in high_three_options(three):
        for x,y,z in a7:
            s.add((u|x)&(v|y)&(w|z))
    s=set(map(canon,s))
    # The target masks are unrestricted up to cyclic translation on the lower base.
    keep=[]; orbits={}
    for x in sorted(s,key=int.bit_count,reverse=True):
        if not x:continue
        if any(x&y==x for ys in orbits.values() for y in ys):continue
        keep.append(x)
        orbits[x]=tuple({((x<<i)&FULL)|(x>>(120-i)) for i in range(120) if x>>(120-i)&1 or i==0})
    return tuple(keep) or (0,)

@cache
def exact(A):
    seven=tuple(d//7 for d in A if d%7==0)
    top=tuple(d//3 for d in A if d%7 and d%9==0)
    low=tuple(d for d in A if d%7 and d%9 and d%16)
    if 16 in A and 48 in A:low=tuple(sorted(low+(24,)))
    return any(fill(low,FULL^h) for h in allowance(seven,top))

