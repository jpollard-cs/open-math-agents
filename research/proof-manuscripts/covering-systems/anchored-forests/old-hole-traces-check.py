"""Enumerate actual row choices and compare the mean with the joint-trace product."""
from fractions import Fraction
from itertools import combinations, product
from math import lcm, prod


def verify(holes, labels, rows):
    coordinates = sorted({i for _, support in rows for i in support})
    period = lcm(*(factor for factor, _ in rows))
    traces = sorted({x % period for x in holes})
    positions = [(x, dict(zip(coordinates, values))) for x in traces
                 for values in product(*(range(labels[i]) for i in coordinates))]
    choices = []
    predicted = Fraction(len(positions))
    for factor, support in rows:
        residues = sorted({x % factor for x in holes})
        masks = []
        for residue in residues:
            for forbidden in product(*(range(labels[i]) for i in support)):
                mask = sum(1 << j for j, (x, vals) in enumerate(positions)
                           if x % factor == residue and
                           all(vals[i] == v for i, v in zip(support, forbidden)))
                masks.append(mask)
        choices.append(masks)
        predicted *= 1 - Fraction(1, len(residues) * prod(labels[i] for i in support))
    full = (1 << len(positions)) - 1
    total = 0
    minimum = len(positions)
    count = 0
    for assignment in product(*choices):
        left = full
        for mask in assignment:
            left &= ~mask
        survivors = left.bit_count()
        total += survivors
        minimum = min(minimum, survivors)
        count += 1
    assert Fraction(total, count) == predicted
    if minimum:
        assert predicted >= 1
    return count, minimum


if __name__ == '__main__':
    # Factors 2,3,6 may be viewed as dressings at fresh primes 5,7,11.
    rows = ((2, (0,)), (3, (0,)), (6, (1,)), (2, (0, 1)), (3, (0, 1, 2)))
    totals = [0, 0, 0]
    for holes in ((0,), (0, 1), (0, 2, 3), (0, 1, 2, 4, 5)):
        for size in range(4):
            for subfamily in combinations(rows, size):
                count, minimum = verify(holes, (2, 2, 3), subfamily)
                totals[0] += 1
                totals[1] += count
                totals[2] += bool(minimum)
    assert verify((0, 1), (2,), ((3, (0,)), (5, (0,)), (7, (0,)))) == (64, 1)
    old_holes = (40, 100, 160, 340)
    lifts = [x for x in range(11*420) if x % 420 in old_holes]
    factors = [7*a for a in range(1, 61) if 60 % a == 0][:11]
    assert len(lifts) == 44 and len(factors) == 11
    assert all(len({x % (11*a) for x in lifts}) == 44 for a in factors)
    print('joint trace tests, assignments, universally noncovering tests:', *totals)
    print('two-site example: 64 assignments, minimum exactly one survivor')
