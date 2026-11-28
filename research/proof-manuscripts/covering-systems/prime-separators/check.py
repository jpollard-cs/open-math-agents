"""Independent finite checks for the prime-separator manuscript."""
from fractions import Fraction
from itertools import product, combinations
from math import lcm, prod, log, exp
from operator import or_
from functools import reduce
from pathlib import Path
import json


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def example():
    # The seed contains two nonzero 2-digits and two pairs of nonzero
    # 3-digits. Its left-over residue is 0 mod 36.
    ordinary = [(2, 1), (4, 2), (3, 1), (6, 2), (9, 3), (18, 6)]
    # The second 3-digit at exponent 1 must cover residue 2 mod 3,
    # and at exponent 2 must cover 6 mod 9. Both are even.
    packet = []
    branches = {}
    for slot, p in enumerate([5, 7, 11, 13]):
        ds = [16, 9] + [d for d in divisors(144) if d not in (16, 9)]
        ds = sorted(ds[:p])
        assert lcm(*ds) == 144
        leaf = slot * 36
        branch = []
        for digit, d in enumerate(ds):
            residue = (leaf + d * ((digit - leaf) * pow(d, -1, p) % p)) % (d * p)
            branch.append((d * p, residue))
        branches[p] = branch
        packet.extend(branch)
    rows = ordinary + packet
    assert len(rows) == len(set(n for n, _ in rows)) == 42
    assert max(n for n, _ in rows) == 624
    period = lcm(*(n for n, _ in rows))
    coverage = bytearray(period)
    for n, a in rows:
        coverage[a::n] = bytes([1]) * (period // n)
    assert all(coverage) and period == 720720
    print('42 distinct moduli; maximum 624; all', period, 'residues covered')
    return ordinary, branches, rows


def ordinary_checks(ordinary, branches):
    # Search freely reassigned residues, using the exact 36-point base.
    # Each complete p-group can fill at most one residue mod 144, since
    # its p cofactors have LCM 144. An incomplete group cannot fill any.
    ms = [n for n, _ in ordinary]
    masks = {n: [sum(1 << z for z in range(a, 36, n)) for a in range(n)] for n in ms}
    thresholds = []
    for dropped in [None] + ms:
        used = [n for n in ms if n != dropped]
        count = min(36 - reduce(or_, v).bit_count() for v in product(*(masks[n] for n in used)))
        thresholds.append(count)
    assert thresholds == [1, 7, 2, 4, 4, 2, 2]
    assert 4 * thresholds[0] > len(branches) - 1
    assert all(4 * h > len(branches) for h in thresholds[1:])
    for p, rows in branches.items():
        assert len(rows) == p and lcm(*(n // p for n, _ in rows)) == 144
        assert all(n % p == 0 for n, _ in rows)
    print('Minimum ordinary holes mod 36, all rows then one deletion:', thresholds)
    print('All 42 single deletions excluded with arbitrary reassignments by fibre contraction.')


def graph_number(rows):
    def factors(n):
        return {p for p in range(2, n+1) if n % p == 0 and
                all(p % d for d in range(2, int(p**0.5)+1))}
    edges = set()
    for n, _ in rows:
        edges.update(combinations(sorted(factors(n)), 2))
    vertices = sorted(set().union(*edges))
    for r in range(len(vertices) + 1):
        covers = [x for x in combinations(vertices, r) if all(set(x).intersection(e) for e in edges)]
        if covers:
            assert covers == [(2, 3)]
            print('Unique minimum vertex cover of actual prime graph:', covers[0])
            return


def harmonic_swap():
    ps = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]
    comparisons = 0
    first = {}
    for r in range(11):
        values = []
        for hs in combinations(ps, r):
            val = prod(Fraction(p, p-1) for p in hs) * (1 + sum(Fraction(1, p-1) for p in ps if p not in hs))
            values.append(val)
            if list(hs) == ps[:r]:
                first[r] = val
        assert max(values) == first[r]
        comparisons += len(values)
    print('Exact rational Euler-product maximization:', comparisons, 'subsets')
    lo, hi = 0., .5
    for _ in range(80):
        mid = (lo+hi)/2
        if exp(0.5772156649015329)*mid*(1+log(1/(2*mid))) < .5:
            lo = mid
        else:
            hi = mid
    print('Root of the necessary exponent equation (numerical):', round(hi, 9))


if __name__ == '__main__':
    ordinary, branches, rows = example()
    ordinary_checks(ordinary, branches)
    graph_number(rows)
    harmonic_swap()
    Path(__file__).with_name('witness-42.json').write_text(json.dumps(rows, separators=(',', ':'))+'\n')
