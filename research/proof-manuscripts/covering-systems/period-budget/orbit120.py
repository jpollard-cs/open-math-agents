from pathlib import Path
import ctypes as C
from functools import cache
lib=C.CDLL(str(Path(__file__).resolve().parent/'symmetry120.so'))
W=C.c_uint64
orbit=lib.orbit120
orbit.argtypes=[C.c_int,C.POINTER(W),C.POINTER(C.c_int)]
orbit.restype=C.c_int
def representatives(masks):
    words=(W*(2*len(masks)))(*(v>>(64*i)&((1<<64)-1) for v in masks for i in range(2)))
    idx=(C.c_int*len(masks))()
    n=orbit(len(masks),words,idx)
    return tuple(sorted((masks[idx[i]] for i in range(n)),key=int.bit_count,reverse=True))
