"""Direct finite checks with free residue changes. Python 3, standard library."""
from functools import cache
from itertools import combinations, combinations_with_replacement, permutations, product
from math import gcd, lcm, prod


@cache
def congruence_holes(moduli):
    period = lcm(*moduli)
    free = (1 << period) - 1
    masks = {free}
    for n in moduli:
        classes = [sum(1 << x for x in range(a, period, n)) for a in range(n)]
        masks = {h & ~c for h in masks for c in classes}
    return tuple(masks)


@cache
def covers(moduli):
    return 0 in congruence_holes(moduli)


@cache
def rigid(moduli):
    return covers(moduli) and all(
        not covers(moduli[:i] + moduli[i + 1:]) for i in range(len(moduli))
        if i == 0 or moduli[i] != moduli[i - 1])


def split_tests():
    tests = exact = inseparable = 0
    for period, size in [(6, 5), (8, 5), (12, 5)]:
        divisors = tuple(n for n in range(2, period + 1) if period % n == 0)
        for k in range(2, size + 1):
            for family in combinations_with_replacement(divisors, k):
                if lcm(*family) != period:
                    continue
                for selected in range(1, (1 << k) - 1):
                    left = tuple(n for i, n in enumerate(family) if selected >> i & 1)
                    right = tuple(n for i, n in enumerate(family) if not selected >> i & 1)
                    p, q = lcm(*left), lcm(*right)
                    virtual = tuple(sorted((*left, gcd(p, q))))
                    residual = tuple(sorted(n // gcd(n, p) for n in right))
                    if covers(virtual):
                        assert covers(family) == (covers(left) or covers(residual))
                        # A coverable left side can never occur in an irreducible split.
                        assert rigid(family) == (rigid(virtual) and rigid(residual))
                    if rigid(family):
                        assert covers(virtual) == rigid(residual)
                        if covers(virtual):
                            exact += 1
                        else:
                            inseparable += 1
                    tests += 1
    return tests, exact, inseparable


@cache
def classes(sizes, support):
    points = list(product(*(range(q) for q in sizes)))
    indices = [i for i in range(len(sizes)) if support >> i & 1]
    out = {}
    for j, x in enumerate(points):
        label = tuple(x[i] for i in indices)
        out[label] = out.get(label, 0) | (1 << j)
    return tuple((sum(1 << i for i, a in zip(indices, label) if a), mask)
                 for label, mask in out.items())


@cache
def grid_min(sizes, rows):
    possible = {(1 << prod(sizes)) - 1}
    for support in rows:
        possible = {holes & ~mask for holes in possible for _, mask in classes(sizes, support)}
    return min(h.bit_count() for h in possible)


def induced(sizes, rows, subset):
    chosen = [i for i in range(len(sizes)) if subset >> i & 1]
    alphabets = tuple(sizes[i] for i in chosen)
    shapes = tuple(sorted(sum(1 << j for j, i in enumerate(chosen) if s >> i & 1)
                          for s in rows if not s & ~subset))
    return grid_min(alphabets, shapes)


def closure_tests():
    witnesses = decisions = restricted = distances = 0
    for sizes, limit in [((2, 3), 5), ((2, 2, 2), 6)]:
        full = (1 << len(sizes)) - 1
        options = [(s, a, m) for s in range(1, full + 1)
                   for a, m in classes(sizes, s) if a]
        for k in range(1, limit + 1):
            for witness in combinations(options, k):
                covered = 0
                for _, _, mask in witness:
                    covered |= mask
                ordinary = tuple(sorted(s for s, _, _ in witness))
                for terminal in range(1, full + 1):
                    if (covered | classes(sizes, terminal)[0][1]).bit_count() != prod(sizes):
                        continue
                    family = tuple(sorted((*ordinary, terminal)))
                    if not all(grid_min(sizes, family[:i] + family[i + 1:]) >= 1
                               for i in range(len(family))):
                        continue
                    witnesses += 1
                    restricted += terminal != full
                    for u in range(full + 1):
                        if u & ~terminal:
                            continue
                        closed = all(not (a & u and s & ~u) for s, a, _ in witness)
                        assert closed == (induced(sizes, ordinary, u) == 1)
                        decisions += 1
                    if terminal != full:
                        continue
                    # Independent brute force over orders for the sharp defect estimate.
                    defect = len(ordinary) - sum(p - 1 for p in sizes)
                    best = len(ordinary) + sum(sizes)
                    for order in permutations(range(len(sizes))):
                        stage = [0] * len(sizes)
                        for s in ordinary:
                            last = next(i for i in reversed(order) if s >> i & 1)
                            stage[last] += 1
                        best = min(best, sum(max(0, p - 1 - n) for p, n in zip(sizes, stage)))
                    assert best <= defect
                    distances += best == defect and defect > 0
    return witnesses, decisions, restricted, distances


if __name__ == "__main__":
    print("indexed integer splits, exact rigid splits, inseparable rigid splits:", *split_tests())
    print("covering witnesses, coordinate cuts, proper terminals, positive equality cases:",
          *closure_tests())
