"""Finite checks for optimised-batch-visibility.md, using only Python 3."""
from itertools import product
from math import gcd, lcm, prod

# A stage contains one prime radix and all its permanent rows.
# The last radix includes its zero label. All others omit the zero label.
P = 13
EARLY = [1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 36, 72]
SPECIAL = [5, 7, 11]
stages = [(2, [2]), (2, [4]), (2, [8]), (3, [3, 6]), (3, [9, 18]),
          (P, [P*d for d in EARLY])]
stages += [(r, [P*r*d for d in EARLY[:r-1]]) for r in SPECIAL]
stages += [(2, [16]), (17, [17*d for d in [*range(1, 17), 18]])]


def verify_rows():
    phases = []
    period = 1
    for index, (radix, rows) in enumerate(stages):
        final = index == len(stages)-1
        assert len(rows) == radix-1+final
        # Each class covers at most one extension of an old residue.
        assert all(lcm(period, n) == period*radix for n in rows)
        # A successful terminal forces agreement on the entire old period.
        if final:
            assert lcm(*(gcd(period, n) for n in rows)) == period
        for i, n in enumerate(rows):
            phases.append((n, (period*(i+1)) % n))
        period *= radix
    mods = [n for n, _ in phases]
    assert (len(set(mods)), len(mods), max(mods), period) == (57, 57, 3432, 12252240)
    # Direct integer scan, independent of the prime-stage induction.
    complete, unmarked = bytearray(period), bytearray(period)
    for n, residue in phases:
        visits = bytes([1])*(period//n)
        complete[residue::n] = visits
        if n % P:
            unmarked[residue::n] = visits
    assert all(complete)
    G = prod(SPECIAL)
    assert all(0 in unmarked[g::G] for g in range(G))
    return unmarked.count(0)


def partition_minimum():
    # The two batches have size 13. Outside means any leftover and any
    # reserved p-row combined. The four types have disjoint owners.
    counts = (12, 4, 6, 10)
    projections = []
    profiles = 0
    for A in product(*(range(n+1) for n in counts)):
        if sum(A) != P:
            continue
        for B in product(*(range(n-a+1) for n, a in zip(counts, A))):
            if sum(B) != P:
                continue
            profiles += 1
            sides = [prod(r for r, n in zip(SPECIAL, side[1:]) if n) for side in (A, B)]
            projections.append(max(sides))
    assert min(projections) == 11
    # This is attained on the actual aligned old rows by putting all
    # 7-side special rows outside and keeping 5 and 11 separate.
    A, B = (9,4,0,0), (3,0,0,10)
    assert sum(A) == sum(B) == P
    assert [counts[i]-A[i]-B[i] for i in range(4)] == [0,0,6,0]
    return profiles


def direct_partition_check():
    # Tiny independent comparison of the type DP with individual row subsets.
    from itertools import combinations
    pool = (1,1,1,1,2,2,3,3)
    indices = set(range(len(pool)))
    direct = set()
    for A in combinations(indices, 3):
        for B in combinations(indices-set(A), 3):
            direct.add(tuple(tuple(sum(pool[i] == t for i in side) for t in (1,2,3))
                             for side in (A,B)))
    types = (4,2,2)
    grouped = {(A,B) for A in product(*(range(n+1) for n in types)) if sum(A)==3
               for B in product(*(range(n-a+1) for n,a in zip(types,A))) if sum(B)==3}
    assert direct == grouped
    return len(grouped)


if __name__ == '__main__':
    print('57 moduli, maximum 3432, period 12252240; deletion holes', verify_rows())
    print('Every residue modulo 385 is seen; integer coverage and stage certificates pass.')
    print('Ordered type profiles for the two actual batches:', partition_minimum())
    print('Exact minimum of the larger visibility is 11.')
    print('Tiny direct-subset cross-check:', direct_partition_check(), 'profiles')
