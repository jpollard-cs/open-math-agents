"""First two prescribed-maximum cardinality layers, with independent small checks."""
from itertools import combinations, product
from math import lcm
from odd_first_size import factors, budget, divisors
from one_hole_search import full_period_defect_one, match, nullity_one_covers


def first_two_layers(m):
    """Least size when <= B(m)+2. None certifies both sizes are impossible."""
    if m < 2:
        raise ValueError("largest modulus must be at least two")
    fs = factors(m)
    prefix = 1
    zero = True
    for p, a in fs:
        zero &= prefix >= p - 1 + (p == fs[-1][0])
        prefix *= a + 1
    if zero:
        return budget(m) + 1
    if sum(a for p, a in fs if p != 2) < 2:
        return None
    prefix = 1
    for p, a in factors(2 * m):
        if p != 2 and prefix < p - 1 + 2 * (p == fs[-1][0]):
            return None
        prefix *= a + 1
    return budget(m) + 2


def compare_candidates(cap):
    candidates = 0
    for m in range(2, cap + 1):
        found = None
        for k in (budget(m) + 1, budget(m) + 2):
            for period in (m, 2 * m):
                if k < budget(period) + 1:
                    continue
                digits = [(p, p**j) for p, a in factors(period) for j in range(1, a + 1)]
                sizes = tuple(p for p, power in digits)
                caps = tuple(p - 1 for p in sizes)
                ds = [n for n in divisors(period) if 1 < n < m]
                for sub in combinations(ds, k - 1):
                    ns = (*sub, m)
                    if lcm(*ns) != period:
                        continue
                    candidates += 1
                    rows = [sum(1 << i for i, (_, power) in enumerate(digits) if n % power == 0)
                            for n in ns]
                    if k == budget(period) + 1:
                        yes = (all(None not in match(rows[:i] + rows[i + 1:], caps)
                                   for i in range(k))
                               and nullity_one_covers(sizes, rows))
                    else:
                        assert period == m
                        yes = full_period_defect_one(sizes, rows[:-1]) is not None
                    if yes and found is None:
                        found = k
        assert found == first_two_layers(m), (m, found, first_two_layers(m))
    return candidates


def check_rectangles():
    tests = 0
    for p, q in ((2, 3), (3, 5), (4, 5), (4, 6), (5, 7)):
        grid = (1 << (p * q)) - 1
        lines = ([sum(1 << (i * q + j) for j in range(q)) for i in range(p)],
                 [sum(1 << (i * q + j) for i in range(p)) for j in range(q)])
        for a, b in product(range(p), range(q)):
            for left in combinations(lines[0], a):
                for right in combinations(lines[1], b):
                    holes = grid & ~(sum(left) | sum(right))
                    assert holes.bit_count() == (p-a)*(q-b)
                    tests += 1
    return tests


def explicit_rectangle():
    H, p, q = 256, 11, 13
    ds = divisors(H)
    # Every guard selects residue zero on its small-prime divisor.
    rows = [(2**i, 2**(i-1)) for i in range(1,9)]
    for r in (p,q):
        for value,d in enumerate(ds, 1):
            rows.append((r*d, d*(value*pow(d,-1,r) % r)))
    cells = list(product((0,10),(0,10,11,12)))
    guards = [H] + ds[:len(cells)-1]
    for (i,j),d in zip(cells,guards):
        z = next(x for x in range(p*q) if x%p == i and x%q == j)
        rows.append((d*p*q,d*(z*pow(d,-1,p*q) % (p*q))))
    period = H*p*q
    assert len(dict(rows)) == len(rows) == 34 and max(dict(rows)) == period
    covered = bytearray(period)
    for n,a in rows:
        covered[a::n] = bytes([1])*(period//n)
    assert all(covered)
    return period, len(rows)


if __name__ == '__main__':
    print('all actual-period candidates for all maxima 2..64:', compare_candidates(64))
    print('individual line selections checked by bit mask:', check_rectangles())
    print('full integer residue period checked and size:', explicit_rectangle())
    for m in (140,330,462,1365,3003,36608):
        print(m, first_two_layers(m))
