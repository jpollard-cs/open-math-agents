"""Separate decision using seven buckets and the upper binary digit."""
from functools import cache,lru_cache
from itertools import product
from math import gcd
from fibre import partitions
from pathlib import Path
import ast
L=360
F=(1<<L)-1
K=180
G=(1<<K)-1
@cache
def row(d,b):
    f=((1<<b)-1)//((1<<d)-1)
    return tuple(f<<i for i in range(d))
def rotation(m,s,b):
    return ((m<<s)&((1<<b)-1))|(m>>(b-s))
def maximize(it):
    best=[]
    for m in sorted(set(it),key=int.bit_count,reverse=True):
        if not any(m&v==m for v in best):best.append(m)
    return best
@cache
def clipped(ds,m):
    vals=[0]
    for d in ds: vals=maximize(x|(y&m) for x in vals for y in row(d,L))
    return vals
@cache
def shapes(ds):
    if len(ds)<7:return (0,)
    out=set()
    for groups in partitions(ds,7):
        single=max(g[0] for g in groups if len(g)==1)
        groups.remove((single,))
        vals=[row(single,L)[0]]
        for g in sorted(groups,key=lambda a:(len(a),-max(a))):
            vals=maximize(y for m in vals for y in clipped(g,m))
        out.update(vals)
    def canon(m):
        return min(rotation(m,i,L) for i in range(L))
    best=[];orb=set()
    for m in sorted(set(map(canon,out)),key=int.bit_count,reverse=True):
        if not any(m&z==m for z in orb):
            best.append(m);orb.update(rotation(m,i,L) for i in range(L))
    return tuple(best)
@cache
def paired7(ds):
    bits=set()
    for m in shapes(ds):
        # Independent cyclic low-coordinate translations are valid automorphisms.
        # Generate the actual cyclic rotations to keep all relative high digit phases.
        for t in range(L):
            Z=rotation(m,t,L); u=v=0
            while Z:
                vbit=Z & -Z
                i=vbit.bit_length()-1
                if i%8<4:u|=1<<(i%K)
                else:v|=1<<(i%K)
                Z^=vbit
            bits.add((u,v))
    return tuple(bits)
from digit_orbits import blocks
def halves(ds):
    return blocks(tuple(2*d for d in ds),2,180)
def canon(m):
    if not m:return 0
    q=m; mi=None
    while q:
        bit=q&-q; q^=bit
        v=rotation(m,K-(bit.bit_length()-1),K)
        mi=v if mi is None else min(v,mi)
    return mi
@cache
def possible(s,t):
    rows=paired7(s)
    out=set()
    for a,b in halves(t):
        out.update((a|x)&(b|y) for x,y in rows)
    return tuple(sorted(set(map(canon,out)),key=int.bit_count,reverse=True))
@lru_cache(maxsize=300000)
def fill(ds,m):
    if not m:return True
    if not ds:return False
    cover=[sorted({m&r for r in row(d,K)},key=int.bit_count,reverse=True) for d in ds]
    bound=sum(opts[0].bit_count() for opts in cover)
    if bound<m.bit_count():return False
    # Force the row with the fewest residues consistent with the upper bound.
    slack=bound-m.bit_count()
    i=min(range(len(ds)),key=lambda j:sum(z.bit_count()>=max(1,cover[j][0].bit_count()-slack) for z in cover[j]))
    if cover[i][0]==0:return fill(ds[:i]+ds[i+1:],m)
    req=max(1,cover[i][0].bit_count()-slack)
    return any(fill(ds[:i]+ds[i+1:],m^z) for z in cover[i] if z.bit_count()>=req)
@cache
def with_pair(s,t):
    from digit_orbits import orbits
    ds=tuple(2*d for d in t)+(24,40)
    patterns=set()
    for rr in orbits(ds):
        if rr[-2]%8!=rr[-1]%8:continue
        pair=[0,0]
        for r,d in zip(rr,ds):
            pair[(r%8)//4]|=row(d//2,K)[r%(d//2)]
        patterns.add(tuple(pair))
    bits=paired7(s); out=set()
    for a,b in patterns:
        out.update((a|x)&(b|y) for x,y in bits)
    return tuple(sorted(set(map(canon,out)),key=int.bit_count,reverse=True))
@cache
def decide(A):
    from math import lcm
    s=tuple(d//7 for d in A if d%7==0)
    binary=[d//2 for d in A if d%16==0]
    base=[d for d in A if d%7 and d%16]
    if len(binary)==2:base.append(lcm(*binary))
    t=tuple(sorted(d//2 for d in base if d%8==0))
    low=tuple(sorted(d for d in base if d%8))
    opts=with_pair(s,t) if len(binary)==3 else possible(s,t)
    from compiled_fill import check
    return check(180,low,opts)
if __name__=="__main__":
    import sys
    if sys.argv[1:]:
        import json
        todo=json.loads(Path(sys.argv[1]).read_text())
    else:todo=ast.literal_eval(Path('cap70-checks.txt').read_text().splitlines()[-1])
    for i,A in enumerate(todo):
        A=tuple(A)
        if sum(d in A for d in (16,48,80))==1:continue
        d=next((d for d in (80,72,70,63,2,3,4,5,6,9,7,16,48,*A) if d in A and decide(tuple(t for t in A if t!=d))),None)
        print(i+1,'removable',d,'irreducible',not d and decide(A),flush=True)
