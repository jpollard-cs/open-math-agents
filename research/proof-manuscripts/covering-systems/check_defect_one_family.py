"""Exact checks for the recursive defect-one family in Erdős #1189."""

from math import lcm


def seed():
    return {
        2: 1, 3: 1, 5: 4, 6: 2, 9: 0,
        10: 8, 15: 0, 18: 6, 30: 6, 45: 12,
    }, 72, 12


def expected_moduli(e):
    return set([2, 3, 5, 6, 10, 15]
               + [2 * 3**j for j in range(2, e + 1)]
               + [10 * 3**j for j in range(1, e)]
               + [3**e, 5 * 3**e])


def extend(classes, e, a, c):
    """Extend S_(e-1) to S_e; return the two new distinguished holes."""
    q = 10 * 3**(e - 1)
    r = 3**(e - 1)
    del classes[r]
    del classes[5 * r]
    classes[q] = a % q
    classes[3 * r] = c % (3 * r)
    classes[6 * r] = (c + q) % (6 * r)
    classes[15 * r] = (c + 2 * q) % (15 * r)
    return c, c + 2 * q


def coverage_counts(classes, period):
    counts = [0] * period
    owners = [None] * period
    for modulus, residue in classes.items():
        for x in range(residue, period, modulus):
            counts[x] += 1
            owners[x] = modulus if counts[x] == 1 else None
    return counts, owners


def divisor_count(e, alpha, beta, gamma):
    m = 2**alpha * 3**beta * 5**gamma
    return sum(m % d == 0 for d in expected_moduli(e))


def check_through(max_e=10):
    classes, a, c = seed()
    for e in range(2, max_e + 1):
        if e > 2:
            a, c = extend(classes, e, a, c)
        period = 10 * 3**e
        assert set(classes) == expected_moduli(e)
        assert lcm(*classes) == period
        counts, owners = coverage_counts(classes, period)
        assert min(counts) >= 1
        private = {m: 0 for m in classes}
        for owner in owners:
            if owner is not None:
                private[owner] += 1
        assert min(private.values()) >= 1
        top = {3**e, 5 * 3**e}
        remaining = {m: r for m, r in classes.items() if m not in top}
        holes = [x for x, count in enumerate(
            coverage_counts(remaining, period)[0]) if count == 0]
        assert holes == sorted([a, c])

        equality_cases = []
        for alpha in (0, 1):
            for gamma in (0, 1):
                for beta in range(e + 1):
                    if alpha == beta == gamma == 0:
                        continue
                    available = divisor_count(e, alpha, beta, gamma)
                    simpson = 1 + alpha + 2 * beta + 4 * gamma
                    assert available <= simpson
                    if available == simpson:
                        equality_cases.append((alpha, beta, gamma))
        assert equality_cases == [(1, e, 1)]
        print(e, len(classes), max(classes), holes, min(private.values()))


if __name__ == "__main__":
    check_through()
