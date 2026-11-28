"""Compare free-placement algorithms to independent enumeration of unions."""
from functools import cache
from itertools import combinations_with_replacement, product
from math import prod
from one_hole_search import full_period_defect_one, match, nullity_one_covers, one_hole


@cache
def uncovered(sizes, rows):
    period = prod(sizes)
    if not rows:
        return frozenset([(1 << period) - 1])
    masks = {}
    for j, point in enumerate(product(*(range(n) for n in sizes))):
        pattern = tuple(point[i] for i in range(len(sizes)) if rows[-1] >> i & 1)
        masks[pattern] = masks.get(pattern, 0) | (1 << j)
    return frozenset(h & ~m for h in uncovered(sizes, rows[:-1]) for m in masks.values())


def holes_in_witness(sizes, boxes):
    return [x for x in product(*(range(n) for n in sizes))
            if not any(all(x[i] == a for i, a in box.items()) for box in boxes)]


def compare():
    queries = decisions = rigid = positive = 0
    for sizes, slack in [((2, 3), 3), ((3, 3), 2), ((2, 2, 2), 2), ((2, 2, 3), 1)]:
        full = (1 << len(sizes)) - 1
        caps = [p - 1 for p in sizes]
        budget = sum(caps)
        for k in range(1, budget + slack + 1):
            for rows in combinations_with_replacement(range(1, full + 1), k):
                possibilities = uncovered(sizes, rows)
                if match(rows, caps).count(None) <= 1:
                    assert nullity_one_covers(sizes, rows) == (0 in possibilities)
                    decisions += 1
                if k < budget:
                    continue
                w = one_hole(sizes, rows)
                assert (w is not None) == any(x.bit_count() == 1 for x in possibilities), (sizes, rows)
                if w is not None:
                    assert holes_in_witness(sizes, w) == [(0,) * len(sizes)]
                queries += 1
                if k == budget + 1:
                    allrows = (*rows, full)
                    actual = 0 in uncovered(sizes, allrows) and all(
                        0 not in uncovered(sizes, allrows[:i] + allrows[i + 1:])
                        for i in range(len(allrows)))
                    cert = full_period_defect_one(sizes, rows)
                    assert actual == (cert is not None)
                    if actual:
                        assert not holes_in_witness(sizes, cert)
                        positive += 1
                    rigid += 1
    print("one-hole comparisons, nullity-at-most-one comparisons, strong decisions, rigid positives:",
          queries, decisions, rigid, positive, flush=True)


def integer_example():
    sizes = (2, 2, 2, 3, 5)
    positions = (2, 4, 8, 3, 5)
    moduli = (2, 4, 8, 3, 5, 10, 20, 15, 30, 60, 120)
    shapes = [sum(1 << i for i, power in enumerate(positions) if n % power == 0)
              for n in moduli]
    cert = full_period_defect_one(sizes, shapes[:-1])
    assert cert is not None
    digits = lambda x: (x % 2, x // 2 % 2, x // 4 % 2, x % 3, x % 5)
    residues = [next(x for x in range(n) if all(digits(x)[i] == a for i, a in b.items()))
                for n, b in zip(moduli, cert)]
    assert all(any(x % n == a for n, a in zip(moduli, residues)) for x in range(120))
    print("period 120, moduli and checked residues:", list(zip(moduli, residues)))


if __name__ == "__main__":
    integer_example()
    compare()
