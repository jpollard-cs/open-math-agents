"""Pass bit masks to the C++ residue enumerator; no solver packages required."""
import ctypes as C
from pathlib import Path
f=C.CDLL(str(Path(__file__).parent.resolve()/'holecheck.so')).check_holes
f.argtypes=[C.c_int,C.c_int,C.POINTER(C.c_int),C.c_int,C.POINTER(C.c_uint64)]
f.restype=C.c_int
def check(base,ds,allowed):
    ds=tuple(ds);allowed=list(allowed)
    full=(1<<base)-1
    values=[(full ^ m)>>(64*j)&((1<<64)-1) for m in allowed for j in range(3)]
    return bool(f(base,len(ds),(C.c_int*len(ds))(*ds),len(allowed),(C.c_uint64*len(values))(*values)))
