"""First admissible cardinality layer for an odd prescribed largest modulus."""
from itertools import combinations
from math import gcd, lcm, prod
from one_hole_search import full_period_defect_one, match, nullity_one_covers


def factors(n):
    fs = []
    p = 2
    while p * p <= n:
        if n % p == 0:
            a = 0
            while n % p == 0:
                a += 1
                n //= p
            fs.append((p, a))
        p = 3 if p == 2 else p + 2
    if n > 1:
        fs.append((n, 1))
    return fs


def divisors(n):
    out = [1]
    for p, a in factors(n):
        out = [v * p**j for v in out for j in range(a + 1)]
    return sorted(out)


def first_size(m):
    if m <= 1 or m % 2 == 0:
        raise ValueError("expected odd m greater than one")
    fs = factors(m)
    count = 2
    for p, a in fs:
        if count < p - 1 + (2 if p == fs[-1][0] else 0):
            return None
        count *= a + 1
    return 2 + sum(a * (p - 1) for p, a in fs)


def construct(m):
    if first_size(m) is None:
        return None
    rows = [(2, 1)]
    previous = 1
    fs = factors(m)
    for p, a in fs:
        for j in range(1, a + 1):
            power = p**j
            guards = [d for d in divisors(2 * previous) if power * d < m]
            for value, d in enumerate(guards[:p - 1], 1):
                residue = d * ((value * (power // p) * pow(d, -1, power)) % power)
                rows.append((d * power, residue))
        previous *= p**a
    rows.append((m, 0))
    assert len(rows) == first_size(m) == len(dict(rows))
    return sorted(rows)


def budget(n):
    return sum(a * (p - 1) for p, a in factors(n))


def independent_check(m, rows):
    period = 2 * m
    assert lcm(*(n for n, _ in rows)) == period
    assert all(1 < n <= m and 0 <= a < n for n, a in rows)
    # Direct coverage over a period and the Znam-Simpson bound on every deletion.
    covered = bytearray(period)
    for n, a in rows:
        covered[a::n] = bytes([1]) * (period // n)
    assert all(covered)
    for t in divisors(period)[:-1]:
        assert sum(t % n == 0 for n, _ in rows) <= budget(t)
    assert len(rows) == budget(period) + 1


def comparisons(cap):
    candidates = positives = 0
    for m in range(3, cap + 1, 2):
        k = budget(m) + 2
        found = False
        for period in (m, 2 * m):
            digits = [(p, p**j) for p, a in factors(period) for j in range(1, a + 1)]
            sizes = tuple(p for p, _ in digits)
            ds = [n for n in divisors(period) if 1 < n < m]
            for subset in combinations(ds, k - 1):
                ns = (*subset, m)
                if lcm(*ns) != period:
                    continue
                candidates += 1
                shapes = [sum(1 << i for i, (_, power) in enumerate(digits) if n % power == 0)
                          for n in ns]
                if period == m:
                    works = full_period_defect_one(sizes, shapes[:-1]) is not None
                else:
                    caps = [p - 1 for p in sizes]
                    works = (all(None not in match(shapes[:i] + shapes[i + 1:], caps)
                                 for i in range(len(ns)))
                             and nullity_one_covers(sizes, shapes))
                found |= works
        assert found == (first_size(m) is not None)
        positives += int(found)
    return candidates, positives


if __name__ == "__main__":
    print("odd maxima through 241, all actual-period candidates and positive maxima:", comparisons(241))
    positive = [m for m in range(3, 100001, 2) if first_size(m) is not None]
    for m in positive:
        independent_check(m, construct(m))
    print("checked periods and every proper divisor budget through largest modulus 100000:", len(positive))
    for m in (1365, 3003):
        print("largest modulus, decision:", m, first_size(m))
