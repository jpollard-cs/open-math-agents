"""Verify the size-31 witness by eliminating the next binary digit before the ternary digit."""
from functools import cache
from pathlib import Path
from itertools import combinations
from math import lcm
import ctypes as C
import json,sys
from binary84 import paired7,canon
from binary90 import lib,pack
from compiled_fill import check
from digit_orbits import orbits
from decide96 import binary_choices
from witness96 import virtual

@cache
def projected(d,r):
    return sum(1<<(x%180) for x in range(360) if x%8//4==r%8//4 and virtual(d,r,x))

@cache
def binary_pairs(ds):
    periods=tuple(d if d>0 else 24 if d==-3 else 120 for d in ds)
    pairs=set()
    for rr in orbits(periods):
        parts=[0,0]
        for d,r in zip(ds,rr):parts[r%8//4]|=projected(d,r)
        pairs.add(tuple(parts))
    return tuple(pairs)

@cache
def high(s,ds):
    vs=binary_pairs(ds); zs=paired7(s); n=C.c_int()
    ptr=lib.combinations180(pack(vs),len(vs),pack(zs),len(zs),C.byref(n))
    try:
        opt={canon(ptr[3*i]|(ptr[3*i+1]<<64)|(ptr[3*i+2]<<128)) for i in range(n.value)}
    finally: lib.free120(ptr)
    return tuple(sorted(opt,key=int.bit_count,reverse=True))

def decide_other(A):
    base=[d for d in A if d%32]
    if sum(d%32==0 for d in A)==2:base.append(48)
    hi=tuple(sorted(d//2 for d in base if d%16==0))
    seven=tuple(sorted(d//7 for d in base if d%7==0))
    remaining=[d for d in base if d%7 and d%16]
    low=tuple(d for d in remaining if d%8)
    eight=tuple(d for d in remaining if d%8==0)
    for choice in binary_choices(hi):
        if check(180,low,high(seven,eight+choice)): return True
    return False
if __name__=='__main__':
    for a in json.loads(Path(sys.argv[1]).read_text()):
        print('whole',decide_other(tuple(a)),flush=True)
        for d in a:
            ans=decide_other(tuple(x for x in a if d!=x))
            print('delete',d,ans,flush=True)
