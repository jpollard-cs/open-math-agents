from functools import cache
from digit_orbits import orbits,blocks
from binary84 import paired7,canon
from compiled_fill import check
import ctypes as C
from pathlib import Path
from math import lcm
from crosscheck import decide as old
import json,sys
U=C.c_uint64
lib=C.CDLL(str(Path(__file__).resolve().parent/'maskcombine.so'))
lib.combinations180.argtypes=[C.POINTER(U),C.c_int,C.POINTER(U),C.c_int,C.POINTER(C.c_int)]
lib.combinations180.restype=C.POINTER(U)
lib.free120.argtypes=[C.POINTER(U)]
def pack(vs):
    return (U*(6*len(vs)))(*(v>>(64*j)&((1<<64)-1) for w in vs for v in w for j in range(3)))
@cache
def allowance(s,t,virt):
    if virt:
        ds=tuple(2*d for d in t)+(24,40);vs=set()
        for rr in orbits(ds):
            if rr[-2]%8!=rr[-1]%8:continue
            mask=[0,0]
            for d,r in zip(ds,rr):mask[(r%8)//4]|=(((1<<180)-1)//((1<<(d//2))-1))<<(r%(d//2))
            vs.add(tuple(mask))
    else:vs=blocks(tuple(2*d for d in t),2,180)
    zs=paired7(s);n=C.c_int()
    data=lib.combinations180(pack(vs),len(vs),pack(zs),len(zs),C.byref(n))
    try: ans={canon(data[3*i]|(data[3*i+1]<<64)|(data[3*i+2]<<128)) for i in range(n.value)}
    finally:lib.free120(data)
    return tuple(sorted(ans,key=int.bit_count,reverse=True))
@cache
def decision(A):
    s=tuple(d//7 for d in A if d%7==0)
    binary=[d//2 for d in A if d%16==0]
    base=[d for d in A if d%7 and d%16]
    if len(binary)==2:base.append(lcm(*binary))
    t=tuple(sorted(d//2 for d in base if d%8==0))
    low=tuple(sorted(d for d in base if d%8))
    return check(180,low,allowance(s,t,len(binary)==3))
if __name__=='__main__':
    for A in json.loads(Path(sys.argv[1]).read_text()):
        A=tuple(A);print('whole set covers',decision(A),flush=True)
        for d in A:
            c=decision(tuple(t for t in A if t!=d));print('delete',d,'covers',c,flush=True);assert not c
