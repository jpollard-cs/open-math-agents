"""Classify the nine-point midpoint patterns that can prevent two-coloring."""
from functools import cache, reduce
from itertools import combinations
from math import gcd
import argparse


def primitive(v):
    g = reduce(gcd, v, 0)
    return tuple(x // g for x in v)


def intersect(rays, signs):
    positive = [(r, s) for r, s in zip(rays, signs) if s > 0]
    negative = [(r, -s) for r, s in zip(rays, signs) if s < 0]
    generated = {r for r, s in zip(rays, signs) if s == 0}
    for u, a in positive:
        for v, b in negative:
            generated.add(primitive(tuple(b*x + a*y for x, y in zip(u, v))))
    # In a nonnegative nullspace cone the extreme rays have minimal supports.
    ordered = sorted((sum(1 << i for i, x in enumerate(r) if x), r) for r in generated)
    minimal = []
    for mask, ray in ordered:
        if all(m & mask != m for m, _ in minimal):
            minimal.append((mask, ray))
    return tuple(ray for _, ray in minimal)


def certify(n):
    triples = list(combinations(range(n), 3))
    colors = []
    for coloring in range(1 << (n-1)):
        mono = sum(1 << h for h, (i,j,k) in enumerate(triples)
                   if (coloring >> i & 1) == (coloring >> j & 1) == (coloring >> k & 1))
        colors.append(mono)
    @cache
    def differences(gaps):
        points = [0]
        for gap in gaps:
            points.append(points[-1] + gap)
        return tuple(points[i] + points[k] - 2*points[j] for i,j,k in triples)

    exceptions = set()
    @cache
    def visit(rays):
        equations = list(zip(*(differences(r) for r in rays)))
        forced = possible = 0
        for i, signs in enumerate(equations):
            lo, hi = min(signs), max(signs)
            if lo == hi == 0:
                forced |= 1 << i
            elif lo < 0 < hi:
                possible |= 1 << i
        best = None
        for mono in colors:
            if mono & forced:
                continue
            branch = mono & possible
            if branch == 0:
                return True
            if best is None or branch.bit_count() < best.bit_count():
                best = branch
        if best is None:
            # The forced graph is uncolorable. Check it and all stricter extensions.
            exceptions.add(forced)
            best = possible
        while best:
            bit = best & -best
            best ^= bit
            child = intersect(rays, equations[bit.bit_length()-1])
            assert all(map(any, zip(*child)))
            if not visit(child):
                return False
        return True

    d = n-1
    axes = tuple(tuple(int(i == j) for j in range(d)) for i in range(d))
    assert visit(axes)
    return exceptions, visit.cache_info()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('size', nargs='?', type=int, choices=(7, 8, 9), default=9)
    n = parser.parse_args().size
    exceptions, stats = certify(n)
    print(f'{n} sites: {len(exceptions)} uncolorable ordered edge patterns; {stats.misses} cones.')
