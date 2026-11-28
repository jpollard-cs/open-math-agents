"""Enumerate column bijections and finite grid packings independently of the criteria."""
from collections import Counter
from functools import lru_cache
from itertools import combinations, combinations_with_replacement, permutations, product
from random import Random

TYPES = tuple(product(range(3), repeat=2))


def masks(cols):
    return Counter((u > 0) + 2 * (v > 0) for u, v in cols)


def zero(left, right):
    a, b = masks(left), masks(right)
    return (a[3] <= b[0] and a[3] + a[1] <= b[0] + b[2]
            and a[3] + a[2] <= b[0] + b[1] and b[3] <= a[0])


def dot(u, v):
    return u[0] * v[0] + u[1] * v[1]


def one(left, right):
    for i, u in enumerate(left):
        for j, v in enumerate(right):
            if dot(u, v) == 1 and zero(left[:i] + left[i+1:], right[:j] + right[j+1:]):
                return True
    return False


@lru_cache(maxsize=1024)
def arrangements(cols):
    return tuple(set(permutations(cols)))


def compare(left, right):
    counts = {min(2, sum(dot(u, v) for u, v in zip(left, perm)))
              for perm in arrangements(right)}
    assert zero(left, right) == (0 in counts)
    assert one(left, right) == (1 in counts)


def packing(q):
    # Enumerate matchings by branching on the first free cell, allowing it to stay unused.
    @lru_cache(None)
    def search(free):
        if free == 0:
            return {(0, 0, 0)}
        mask = free & -free
        u = mask.bit_length() - 1
        rest = free ^ mask
        results = search(rest).copy()
        for v in range(u + 1, 2*q):
            if not (rest >> v) & 1:
                continue
            kind = 0 if u % q == v % q else 1 if u // q == v // q else 2
            for profile in search(rest ^ (1 << v)):
                counts = list(profile)
                counts[kind] += 1
                results.add(tuple(counts))
        return results
    actual = search((1 << (2*q))-1)
    tested = 0
    for v, h, d in product(range(q+2), repeat=3):
        r = q - v
        predicted = v <= q and d <= r and h <= 2*((r-d)//2) and (r,d) != (1,1)
        assert predicted == ((v,h,d) in actual)
        if v+h+d <= q-1:
            assert predicted
        tested += 1
    return tested


if __name__ == '__main__':
    count = 0
    for q in range(1, 4):
        profiles = tuple(combinations_with_replacement(TYPES, q))
        for left, right in product(profiles, repeat=2):
            compare(left, right)
            count += 1
    rng = Random(1189)
    for q in range(4, 8):
        for _ in range(80):
            left, right = (tuple(rng.choices(TYPES, k=q)) for _ in range(2))
            compare(left, right)
            count += 1
    print("Marked profile pairs against explicit permutations:", count)
    print("Pair-type quotas against explicit grid matchings:", sum(packing(q) for q in range(2,8)))
