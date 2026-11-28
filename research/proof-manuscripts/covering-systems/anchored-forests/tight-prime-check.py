"""Direct labelled residue tests and independent prime-tree frontier enumeration."""
from functools import cache
from itertools import product
from math import gcd, prod
from fractions import Fraction


def component_masks(supports):
    # Traverse row nodes using the symmetric condition of sharing a variable.
    unseen = set(range(len(supports)))
    trees = []
    while unseen:
        todo = [unseen.pop()]
        nodes = []
        while todo:
            i = todo.pop()
            nodes.append(i)
            neighbours = {j for j in unseen if set(supports[i]) & set(supports[j])}
            unseen -= neighbours
            todo.extend(neighbours)
        axes = {p for i in nodes for p in supports[i]}
        edges = sum(len(supports[i]) for i in nodes)
        if edges == len(nodes) + len(axes) - 1:
            trees.append(sum(1 << i for i in nodes))
    return trees


def exhaustive(supports, depths, sizes):
    """Compute all feasible active subsets by enumerating actual class labels."""
    points = list(product(*(range(s) for s in sizes)))
    options = []
    for axes, ds in zip(supports, depths):
        choices = []
        for labels in product(*(range(d) for d in ds)):
            mask = sum(1 << j for j, pt in enumerate(points)
                       if all(pt[p] % d == a for p, d, a in zip(axes, ds, labels)))
            choices.append(mask)
        options.append(choices)
    all_points = (1 << len(points)) - 1
    trees = component_masks(supports)
    tested = 0
    for active in range(1 << len(supports)):
        masks = {0}
        for i, choices in enumerate(options):
            if active & (1 << i):
                masks = {a | b for a in masks for b in choices}
        assert (all_points in masks) == any(active & t == t for t in trees)
        tested += 1
    return tested


def prime_patterns():
    cases = 0
    for a in [[2, 2], [2, 4, 4], [4, 4, 4, 4]]:
        b = [3, 3, 3]
        for shared in range(min(len(a), len(b)) + 1):
            supports = [[0, 1]] * shared + [[0]] * (len(a)-shared) + [[1]] * (3-shared)
            depths = [[d, 3] for d in a[:shared]] + [[d] for d in a[shared:]] + [[3]] * (3-shared)
            cases += exhaustive(supports, depths, [max(a), 3])
    # Three-variable tree with one row on three coordinates and a six-edge cycle.
    for supports in [[[0], [1], [2], [0, 1, 2]], [[0, 1], [0, 2], [1, 2]]]:
        cases += exhaustive(supports, [[2]*len(s) for s in supports], [2, 2, 2])
    return cases


def frontier(p, capacities):
    """Integer optimization over unfilled parent cells."""
    @cache
    def best(depth, live):
        if live == 0:
            return 0
        if depth == len(capacities):
            return -10**7
        children = p * live
        return max(t + best(depth + 1, children-t)
                   for t in range(min(capacities[depth], children) + 1))
    return max(-1, best(0, 1))


def check_frontiers():
    n = 0
    for p in [2, 3, 5]:
        for length in range(1, 5):
            for cap in product(range(1, 7), repeat=length):
                if tuple(sorted(cap, reverse=True)) != cap:
                    continue
                total = p**length
                by_lengths = max((sum(choice) for choice in product(*(range(c+1) for c in cap))
                                  if sum(v * p**(length-j-1) for j, v in enumerate(choice)) == total),
                                 default=-1)
                opt = frontier(p, cap)
                assert opt == by_lengths
                tails = [sum(Fraction(c,p**i) for i,c in enumerate(cap[j:],1)) for j in range(1,length)]
                assert opt <= p + (p-1)*sum(int(v) for v in tails)
                n += 1
    return n


def verify_integer_examples():
    rows = [2, 4, 8, 3, 6, 5, 10, 20, 40, 15]
    labels = [1, 2, 4, 0, 4, 0, 6, 12, 8, 14]
    assert all(any(x % n == a for n, a in zip(rows, labels)) for x in range(120))
    cyclic = [n for n in rows if n not in (6, 40)] + [30]
    cases = [rows[:i] + rows[i+1:] for i in range(len(rows))] + [cyclic]
    placements = 0
    for family in cases:
        old_parts = [gcd(n, 8) for n in family]
        supports = [n // d for n, d in zip(family, old_parts)]
        for phases in product(*(range(d) for d in old_parts)):
            placements += 1
            for x in range(8):
                active = [s for d, a, s in zip(old_parts, phases, supports) if x % d == a]
                if 1 in active:
                    continue
                missing_rows = max(0, 3 - active.count(3))
                missing_columns = max(0, 5 - active.count(5))
                if missing_rows * missing_columns > active.count(15):
                    break
            else:
                raise AssertionError("local rectangle exclusions failed")
    print("freely assigned exterior phases excluded", placements)


if __name__ == "__main__":
    verify_integer_examples()
    print("exact active subsets", prime_patterns())
    print("independent finite frontier optima", check_frontiers())
