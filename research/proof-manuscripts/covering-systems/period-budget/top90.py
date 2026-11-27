"""Native enumeration of the same unions/intersections on the 120-cycle."""
from functools import cache
from pathlib import Path
import ctypes as C
from top84 import high_three_options,all7,canon
U=C.c_uint64
lib=C.CDLL(str(Path(__file__).resolve().parent/'maskcombine.so'))
lib.combinations120.argtypes=[C.POINTER(U),C.c_int,C.POINTER(U),C.c_int,C.POINTER(C.c_int)]
lib.combinations120.restype=C.POINTER(U)
lib.free120.argtypes=[C.POINTER(U)]
def pack(vals):
    return (U*(6*len(vals)))(*(n>>(64*j)&((1<<64)-1) for v in vals for n in v for j in (0,1)))
@cache
def allowance(s,t):
    vs=high_three_options(t);zs=all7(s)
    n=C.c_int()
    arr=lib.combinations120(pack(vs),len(vs),pack(zs),len(zs),C.byref(n))
    try:
        shapes={canon(arr[2*i]+(arr[2*i+1]<<64)) for i in range(n.value)}
    finally:lib.free120(arr)
    return tuple(sorted(shapes,key=int.bit_count,reverse=True))
