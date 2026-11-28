"""Recover ordinary and lifted residues from a positive cap-96/105 decision."""
from math import lcm
from functools import cache
from pathlib import Path
import ctypes as C
import json,sys
from decide96 import binary_choices
from compiled_fill import check as native_check
from top90 import allowance
from top84 import all7
from witness72 import top_choices,resolve7
from crosscheck import FULL,row

def virtual(d,r,j):
    if d>0:return j%d==r
    if d==-1:return j%24==r%24 or j%40==r%40
    if d==-2:return j%8==r%8 and (j%3!=r%3 or j%5==r%5)
    if d==-3:return j%8==r%8 and j%3!=r%3
    if d==-4:return j%40==r%40 and j%3!=r%3
    raise ValueError(d)

def check(rows,allowed):
    return native_check(120,rows,allowed)

def binary_residues(ds,target):
    points=[j for j in range(240) if target>>(j%120)&1]
    misses=(1<<len(points))-1
    candidates=[[sum(1<<i for i,x in enumerate(points) if x%d==r) for r in range(d)] for d in ds]
    @cache
    def find(i,remain):
        if not remain:return (0,)*(len(ds)-i)
        if i==len(ds):return None
        if sum(max((remain&m).bit_count() for m in row) for row in candidates[i:]) < remain.bit_count():return None
        for r,m in enumerate(candidates[i]):
            result=find(i+1,remain&~m)
            if result is not None:return (r,)+result
        return None
    result=find(0,misses)
    assert result is not None
    return result

def witness(A):
    ordinary32=[d for d in A if d%32]
    assert 32 in A and 96 in A and 48 in A
    binary=sorted(d for d in ordinary32 if d%16==0)+[48]  # final index is virtual
    sev=tuple(sorted(d//7 for d in ordinary32 if d%7==0))
    tern=tuple(sorted(d//3 for d in ordinary32 if d%7 and d%9==0))
    ordinary=tuple(sorted(d for d in ordinary32 if d%7 and d%9 and d%16))
    shapes=allowance(sev,tern)
    choice=next(c for c in binary_choices(tuple(sorted(d//2 for d in binary))) if check(ordinary+c,shapes))
    rows=ordinary+choice
    left=0;right=len(shapes)
    while right-left>1:
        mid=(left+right)//2
        if check(rows,shapes[left:mid]):right=mid
        else:left=mid
    h=shapes[left]
    shifts={((h<<i)&FULL)|(h>>(120-i)) for i in range(120)}
    masks7=all7(sev)
    for groups,rr,(a,b,c) in top_choices(tern):
        hit=next((v for x,y,z in masks7 if (v:=((a|x)&(b|y)&(c|z))) in shifts),None)
        if hit is None:continue
        rem=FULL^hit
        sol={};projected=0
        for i,d in enumerate(rows):
            size=d if d>0 else 120
            for r in range(size):
                m=sum(1<<j for j in range(120) if virtual(d,r,j))
                if check(rows[i+1:],[FULL^(rem&~m)]):break
            else:raise ValueError('no residue')
            rem &=~m
            if i<len(ordinary):sol[d]=r
            else:projected|=m
        assert not rem
        for d,g,r in zip(tern,groups,rr):
            sol[3*d]=next(n for n in range(3*d) if n%d==r and n%9//3==g)
        holes=[v for v in range(360) if all(v%d!=r for d,r in sol.items()) and not (projected>>(v%120)&1)]
        sol.update(resolve7(sev,holes))
        bs=binary_residues(binary,projected)
        sol.update(zip(binary[:-1],bs[:-1]))
        for bit,d in enumerate((32,96)):
            sol[d]=next(r for r in range(d) if r%(d//2)==bs[-1]%(d//2) and (r//16)%2==bit)
        assert set(sol)==set(A)
        assert all(any(v%d==r for d,r in sol.items()) for v in range(lcm(*A)))
        return sorted(sol.items())
    raise ValueError('no compatible lifts')

if __name__=='__main__':
    for A in json.loads(Path(sys.argv[1]).read_text()):
        print(json.dumps(witness(A)),flush=True)
