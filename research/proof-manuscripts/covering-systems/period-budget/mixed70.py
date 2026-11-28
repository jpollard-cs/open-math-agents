"""Exact coverability at cap 70 by two successive prime-digit eliminations."""
from functools import cache
from itertools import product
from math import gcd
from seven import masks as seven_masks, rotate,L
from crosscheck import row,fill,FULL
from fixed_sizes import OLD,SEVEN
from itertools import combinations,permutations

@cache
def high_three_options(ds):
    """Fix a base translation modulo each prime power and name digit buckets on first use."""
    if not ds: return ((0,0,0),)
    align=[1]*len(ds)
    for primepower in (3,4,5):
        modulus=max(gcd(d,primepower) for d in ds)
        i=next(i for i,d in enumerate(ds) if d%modulus==0)
        align[i]*=modulus
    ans=set()
    for assignment in product(range(3),repeat=len(ds)):
        if assignment[0] or any(x>1+max(assignment[:i]) for i,x in enumerate(assignment) if i):continue
        for vals in product(*(row(d)[::step] for d,step in zip(ds,align))):
            res=[0]*3
            for bucket,mask in zip(assignment,vals):res[bucket]|=mask
            ans.add(tuple(res))
    return tuple(ans)

@cache
def layers(shape):
    out=[0,0,0]
    while shape:
        bit=shape & -shape
        n=bit.bit_length()-1
        out[n%9//3] |= 1<<(n%120)
        shape^=bit
    return tuple(out)

@cache
def all7(ds):
    return tuple({layers(rotate(s,i)) for s in seven_masks(ds) for i in range(L)})

def canon(x):
    if not x:return 0
    # Each orbit has a member with its low bit 1, e.g. the rotation of the least set bit.
    # Align the least member of the subset to origin and minimize over these alignments.
    vals=[]
    Y=x
    while Y:
        low=Y & -Y; t=low.bit_length()-1
        vals.append((x>>t)|((x<<(120-t))&FULL))
        Y^=low
    return min(vals)

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

if __name__=='__main__':
    import ast
    from pathlib import Path
    todo=ast.literal_eval(Path('cap70-checks.txt').read_text().splitlines()[-1])
    yes=[]
    for i,A in enumerate(todo):
        if 16 in A and 48 not in A or 48 in A and 16 not in A: continue
        # Deleting an old ubiquitous row first often gives the shortest positive certificate.
        removable=next((d for d in (63,70,2,3,4,5,6,9,7,16,48,*A) if d in A and exact(tuple(v for v in A if v!=d))),None)
        if not removable and exact(A):yes.append(A)
        print(i+1,"of",len(todo),"removable",removable,"irreducible sets so far",len(yes),flush=True)
    print("size 26, max 70:",yes)
