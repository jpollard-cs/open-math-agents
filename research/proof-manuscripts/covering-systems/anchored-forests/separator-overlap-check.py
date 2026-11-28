"""Compute the binary overlap minimum directly over all column bijections."""
from itertools import combinations_with_replacement, permutations, product


def minimum_formula(a, b):
    q = len(a)
    excess = [sum(bool(x & mask) for x in a+b)-q for mask in (1,2)]
    return max(sum(max(0,x) for x in excess), a.count(3)-b.count(0), b.count(3)-a.count(0))


tested = 0
for q in range(6):
    masks = tuple(combinations_with_replacement(range(4), q))
    placements = {b:set(permutations(b)) for b in masks}
    for left,right in product(masks, repeat=2):
        brute = min(sum((u&v).bit_count() for u,v in zip(left, reordered)) for reordered in placements[right])
        assert brute == minimum_formula(left,right)
        tested += 1
print("Exact minimum versus all column bijections:", tested, "profile pairs")
