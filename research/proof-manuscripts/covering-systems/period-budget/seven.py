"""Project all admissible top-seven assignments, anchored above a lower-level hole."""
from itertools import combinations,product
from functools import cache
from math import lcm
L=360
FULL=(1<<L)-1
@cache
def row(d):
    assert L%d==0
    a=FULL//((1<<d)-1)
    return tuple(a<<i for i in range(d))
def rotate(x,i):
    return ((x<<i)&FULL)|(x>>(L-i))
@cache
def canonical(x):
    return min(rotate(x,i) for i in range(L))
def dominated(x, y):
    return any(x&rotate(y,i)==x for i in range(L))
@cache
def masks(top):
    if len(top)<7:return (0,)
    out=set()
    for anchors in combinations(range(len(top)),7):
        base=[row(top[i])[0] for i in anchors]
        rest=[top[i] for i in range(len(top)) if i not in anchors]
        for dest in product(range(7),repeat=len(rest)):
            plain=FULL
            for j in range(7):
                if j not in dest:plain &= base[j]
            affected=set(dest)
            for vals in product(*(row(d) for d in rest)):
                S=plain
                for j in affected:
                    v=base[j]
                    for i,b in enumerate(dest):
                        if b==j:v |= vals[i]
                    S &=v
                if S not in out:out.add(S)
    shapes=set(map(canonical,out))
    best=[]
    for s in sorted(shapes,key=int.bit_count,reverse=True):
        if not any(dominated(s,b) for b in best):best.append(s)
    return tuple(best)
if __name__=='__main__':
    for ds in [(1,2,3,4,5,6,8,9,10), (1,2,3,4,5,6,8,9),(1,2,3,4,5,6,8,10)]:
        m=masks(ds)
        print(ds,len(m),[(v.bit_count(),next(i for i in range(1,L+1) if rotate(v,i)==v)) for v in m],flush=True)
