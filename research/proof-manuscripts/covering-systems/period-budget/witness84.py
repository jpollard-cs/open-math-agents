"""Lift a feasible binary compound row and the other projected assignments."""
from mod84 import allowance,options
from compiled_fill import check
from top84 import all7
from witness72 import top_choices,resolve7
from crosscheck import FULL
from math import lcm
from pathlib import Path
import json,sys
def construct(A):
    ds=tuple(d//7 for d in A if d%7==0)
    top=tuple(sorted(d//3 for d in A if d%7 and d%9==0))
    low=sorted(d for d in A if d%7 and d%9 and d%16)
    binary=[d//2 for d in A if d%16==0]
    virt=0
    if len(binary)==3:virt=-1
    if len(binary)==2:virt=lcm(*binary)
    if virt:low.append(virt)
    low=sorted(low,key=lambda x: x if x>0 else 17)
    # Find one feasible projected shape, then recover the original unnormalized shape.
    hs=allowance(ds,top)
    assert check(120,low,hs)
    left=0; right=len(hs)
    while right-left>1:
        mid=(left+right)//2
        if check(120,low,hs[left:mid]):right=mid
        else:left=mid
    h=hs[left]
    shifts={((h<<i)&FULL)|(h>>(120-i)) for i in range(120)}
    a7=all7(ds)
    for groups,rr,(a,b,c) in top_choices(top):
        hit=next((((a|x)&(b|y)&(c|z)) for x,y,z in a7 if ((a|x)&(b|y)&(c|z)) in shifts),None)
        if hit is None:continue
        rem=FULL ^ hit; lower=[]
        for i,d in enumerate(low):
            r=next(j for j,v in enumerate(options(d)) if check(120,low[i+1:],[FULL ^ (rem & ~v)]))
            rem &= ~options(d)[r]
            lower.append((d,r))
        for d,g,r in zip(top,groups,rr):
            lower.append((3*d,next(n for n in range(3*d) if n%d==r and n%9//3==g)))
        def covered(n):
            return any((n%d==r if d>0 else n%24==r%24 or n%40==r%40) for d,r in lower)
        holes=[n for n in range(360) if not covered(n)]
        sol=resolve7(ds,holes)
        if virt:
            idx=next(i for i,(d,r) in enumerate(lower) if d==virt)
            _,r=lower.pop(idx)
            if virt==-1:
                sol[16]=r%8
                for d in (48,80):
                    sol[d]=next(j for j in range(d) if j%(d//2)==r%(d//2) and (j%16)//8==1)
            else:
                for bit,m in enumerate(binary):
                    sol[2*m]=next(j for j in range(2*m) if j%m==r%m and (j%16)//8==bit)
        sol.update(lower)
        assert set(sol)==set(A)
        assert all(any(x%d==r for d,r in sol.items()) for x in range(lcm(*A)))
        return sorted(sol.items())
    raise AssertionError('missed a maximal shape')
if __name__=='__main__':
    for A in json.loads(Path(sys.argv[1]).read_text()):print(json.dumps(construct(A)),flush=True)
