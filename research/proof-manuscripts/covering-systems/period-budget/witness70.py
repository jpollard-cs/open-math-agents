"""Reconstruct actual residues and exhaust their full period."""
from pathlib import Path
from itertools import combinations,product
from math import lcm,gcd
from functools import cache
import json,ast
from mixed70 import all7,canon
from crosscheck import FULL,row,fill

def top_choices(ds):
    align=[1]*len(ds)
    for pp in (3,8,5):
        modulus=max(gcd(d,pp) for d in ds)
        align[next(i for i,d in enumerate(ds) if d%modulus==0)]*=modulus
    for groups in product(range(3),repeat=len(ds)):
        if groups[0] or any(x>1+max(groups[:i]) for i,x in enumerate(groups) if i):continue
        for rr in product(*(range(0,d,s) for d,s in zip(ds,align))):
            allowed=[0,0,0]
            for g,d,r in zip(groups,ds,rr):allowed[g]|=row(d)[r]
            yield groups,rr,allowed

def resolve7(ds,holes):
    assert holes
    h=holes[0]; full=(1<<len(holes))-1
    bits={d:tuple(sum(1<<i for i,x in enumerate(holes) if x%d==r) for r in range(d)) for d in ds}
    for anchors in combinations(range(len(ds)),7):
        rest=[i for i in range(len(ds)) if i not in anchors]
        fixed=[bits[ds[i]][h%ds[i]] for i in anchors]
        for groups in product(range(7),repeat=len(rest)):
            if any(fixed[g]!=full for g in range(7) if g not in groups):continue
            for rr in product(*(range(ds[i]) for i in rest)):
                covered=list(fixed)
                for i,g,r in zip(rest,groups,rr):covered[g]|=bits[ds[i]][r]
                if not all(v==full for v in covered):continue
                conf={i:(g,h%ds[i]) for g,i in enumerate(anchors)}
                conf.update({i:(g,r) for i,g,r in zip(rest,groups,rr)})
                return {7*d:next(x for x in range(7*d) if x%7==conf[i][0] and x%d==conf[i][1]) for i,d in enumerate(ds)}
    raise AssertionError("inconsistent full-seven mask")

def construct(A):
    ds=tuple(d//7 for d in A if d%7==0)
    B=[d for d in A if d%7 and d%16]
    pair=16 in A and 48 in A
    if pair:B.append(24)
    top=tuple(sorted(d//3 for d in B if d%9==0))
    low=tuple(sorted(d for d in B if d%9))
    @cache
    def test(y):return fill(low,FULL^y)
    for groups,rr,(a,b,c) in top_choices(top):
        for x,y,z in all7(ds):
            allowed=(a|x)&(b|y)&(c|z)
            if not test(canon(allowed)):continue
            rem=FULL^allowed
            ordinary=[]
            for i,d in enumerate(low):
                r=next(r for r,v in enumerate(row(d)) if fill(low[i+1:],rem & ~v))
                ordinary.append((d,r)); rem &= ~row(d)[r]
            for d,g,r in zip(top,groups,rr):
                R=next(n for n in range(3*d) if n%d==r and n%9//3==g)
                ordinary.append((3*d,R))
            holes=[n for n in range(360) if all(n%d!=r for d,r in ordinary)]
            rs=resolve7(ds,holes)
            if pair:
                i=next(i for i,(d,r) in enumerate(ordinary) if d==24)
                _,r=ordinary.pop(i)
                rs[16]=r%8;rs[48]=next(n for n in (r,r+24) if n%16>=8)
            rs.update(ordinary)
            assert set(rs)==set(A)
            assert all(any(i%d==r for d,r in rs.items()) for i in range(lcm(*A)))
            return sorted(rs.items())
    raise AssertionError("no cover found")

if __name__=="__main__":
    import sys
    if len(sys.argv)>1:sets=json.loads(Path(sys.argv[1]).read_text())
    else:sets=[ast.literal_eval(Path("cap70-checks.txt").read_text().splitlines()[-1])[10]]
    for A in sets:
        print(json.dumps(construct(tuple(A))),flush=True)
