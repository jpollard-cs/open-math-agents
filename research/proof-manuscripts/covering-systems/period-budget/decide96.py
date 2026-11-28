"""Coverability on the eligible modulus pool through 105, with both high binary digits eliminated."""
from functools import cache
import ctypes as C
from math import lcm
from orbit120 import representatives
from top90 import allowance
from compiled_fill import f as check_holes

def binary_choices(top):
    """Return alternative lists of independent residue choices on the 120-cycle.

    Negative codes denote translated compound masks in holecheck.cpp.
    The input is the sorted list of moduli projected from the 16-digit.
    """
    if len(top) < 2:
        return [()]
    if len(top) == 2:
        return [(lcm(*top),)]
    families = {
        (8, 24, 40): [(-1,)],
        (8, 24, 24): [(-3,)],
        (24, 24, 40): [(24,), (-4,)],
        (8, 24, 24, 40): [(24, 40), (-2,)],
    }
    return families[top]

@cache
def masks(seven, ternary):
    full = allowance(seven, ternary)
    result = representatives(full)
    allowance.cache_clear()
    full_mask=(1<<120)-1
    words=[((full_mask ^ m)>>(64*j)) & ((1<<64)-1) for m in result for j in range(3)]
    return len(result),(C.c_uint64*len(words))(*words)

@cache
def decide(moduli):
    """Allow all residues to be chosen anew, including after deletions."""
    lower = [d for d in moduli if d % 32]
    if sum(d % 32 == 0 for d in moduli) == 2:
        lower.append(48)
    binary = tuple(sorted(d // 2 for d in lower if d % 16 == 0))
    seven = tuple(sorted(d // 7 for d in lower if d % 7 == 0))
    ternary = tuple(sorted(d // 3 for d in lower if d % 7 and d % 9 == 0))
    ordinary = tuple(sorted(d for d in lower if d % 7 and d % 9 and d % 16))
    count, words = masks(seven, ternary)
    for choice in binary_choices(binary):
        ds=ordinary+choice
        if check_holes(120,len(ds),(C.c_int*len(ds))(*ds),count,words):
            return True
    return False
