"""Exhaustive small-grid checks for residual-mass.md. Python standard library."""
from functools import cache
from fractions import Fraction as F
from itertools import combinations, product
from math import prod


def grid_check(shape):
    points = list(product(*(range(d) for d in shape)))
    supports = ((0, 1), (0, 2), (1, 2), (0, 1, 2))
    masks = []
    for support in supports:
        cells = {}
        for i, x in enumerate(points):
            key = tuple(x[j] for j in support)
            cells[key] = cells.get(key, 0) | 1 << i
        masks.append(tuple(cells.values()))

    @cache
    def attainable(profile):
        if not any(profile):
            return {0}
        j = next(j for j, t in enumerate(profile) if t)
        previous = tuple(t - (i == j) for i, t in enumerate(profile))
        return {m | c for m in attainable(previous) for c in masks[j]}

    count = 0
    for profile in product(range(3), repeat=len(supports)):
        if (1 << len(points)) - 1 in attainable(profile):
            continue
        for mask in range(1 << len(shape)):
            vertices = [i for i in range(len(shape)) if mask >> i & 1]
            expectation = F(prod(shape[i] for i in vertices))
            for support, t in zip(supports, profile):
                if set(support) <= set(vertices):
                    expectation *= (1 - F(1, prod(shape[i] for i in support)))**t
            assert expectation >= 1
        count += 1
    return count


def clipping_check():
    count = 0
    for q in (2, 3, 5, 7):
        slots = range(1, q + 4)
        for states in product(range(3), repeat=len(slots)):
            unary = [m for m, s in zip(slots, states) if s == 1]
            mixed = [m for m, s in zip(slots, states) if s == 2]
            if len(unary) >= q:
                continue
            mass = sum(F(1, q*m) for m in unary + mixed)
            bound = sum(F(1, q*j) for j in range(1, q))
            bound += sum(F(1, q*max(q, m)) for m in mixed)
            bound -= F(q - 1 - len(unary), q*q)
            assert mass <= bound
            count += 1
    return count


if __name__ == "__main__":
    print("universally noncovering profiles:",
          {shape: grid_check(shape) for shape in ((2, 2, 2), (1, 2, 3), (2, 2, 3))})
    print("integer cofactor patterns checked:", clipping_check())
