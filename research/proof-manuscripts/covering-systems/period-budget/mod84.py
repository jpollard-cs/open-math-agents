"""A 16,48,80 binary fibre contracts to two compatible progressions."""
from itertools import combinations
from functools import cache,lru_cache
from math import lcm
from pathlib import Path
import json
from top84 import allowance
from compiled_fill import check
from crosscheck import row, FULL, decide as old
from fixed_sizes import OLD, SEVEN

@cache
def options(d):
    if d>0:return row(d)
    return tuple(row(24)[i%24]|row(40)[i%40] for i in range(120))

@lru_cache(maxsize=500000)
def fill(ds,holes):
    if holes==0:return True
    if not ds:return False
    parts=[sorted({holes&s for s in options(d)},key=int.bit_count,reverse=True) for d in ds]
    slack=sum(p[0].bit_count() for p in parts)-holes.bit_count()
    if slack<0:return False
    # Tight capacity rows yield the fewest possible branches.
    choices=[sum(z.bit_count()>=max(1,p[0].bit_count()-slack) for z in p) for p in parts]
    i=choices.index(min(choices))
    rest=ds[:i]+ds[i+1:]
    required=max(1,parts[i][0].bit_count()-slack)
    return any(fill(rest,holes ^ z) for z in parts[i] if z.bit_count()>=required)

@cache
def decide(A):
    sev=tuple(d//7 for d in A if d%7==0)
    top=tuple(d//3 for d in A if d%7 and d%9==0)
    low=[d for d in A if d%7 and d%9 and d%16]
    binary=[d//2 for d in A if d%16==0]
    if len(binary)==2:low.append(lcm(*binary))
    if len(binary)==3:low.append(-1)
    low=tuple(sorted(low,key=lambda d:d if d>0 else 17))
    return check(120,low,allowance(sev,top))

if __name__=='__main__':
    P=tuple(sorted(OLD+SEVEN+(16,48,60)))
    assert all(old(A) for A in combinations(P,25))
    yes=[]
    for i,X in enumerate(X for X in combinations(P,24) if not old(X)):
        A=tuple(sorted(X+(63,70,72,80)))
        # Invariant over any starting assignment. Absent critical binary rows can be removed.
        removable=next((d for d in (80,72,70,63,3,4,5,6,7,*A) if d in A and decide(tuple(t for t in A if t!=d))),None)
        if not removable and decide(A):yes.append(A)
        Path('size28-yes.json').write_text(json.dumps(yes)+'\n')
        print(i+1,'removable',removable,'irreducible total',len(yes),flush=True)
