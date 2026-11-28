"""Exhaustive search at the largest sizes up to maximum modulus 56."""
from itertools import combinations
from math import lcm
from functools import cache
from fibre import base_decision
from pathlib import Path
import json

OLD=(2,3,4,5,6,8,9,10,12,15,18,20,24,30,36,40,45)
SEVEN=(7,14,21,28,35,42,56)
@cache
def cover(A):
    mods=list(A)
    if any(d in SEVEN for d in mods):
        full=all(d in mods for d in SEVEN)
        mods=[d for d in mods if d not in SEVEN]
        if full:mods.append(120)
    if 16 in mods or 48 in mods:
        full=16 in mods and 48 in mods
        mods=[d for d in mods if d not in (16,48)]
        if full:mods.append(24)
    return base_decision(tuple(sorted(mods)))

def enumerate_large():
    results={}
    for bits2 in ((),(16,48)):
        for bits7 in ((),SEVEN):
            fixed=bits2+bits7
            for k in range(16,len(OLD)+len(fixed)+1):
                for subset in combinations(OLD,k-len(fixed)):
                    A=tuple(sorted(subset+fixed))
                    if not cover(A):continue
                    if any(cover(A[:i]+A[i+1:]) for i in range(len(A))):continue
                    entry=results.setdefault((max(A),k),[0,A])
                    entry[0]+=1
                if (max(fixed,default=0),k) in results:
                    print(k,max(fixed),results[max(fixed),k],flush=True)
    return [{"max":m,"size":k,"count":v[0],"example":v[1]} for (m,k),v in sorted(results.items())]

if __name__=="__main__":
    r=enumerate_large()
    Path("minima-through-56.json").write_text(json.dumps(r,indent=2)+"\n")
