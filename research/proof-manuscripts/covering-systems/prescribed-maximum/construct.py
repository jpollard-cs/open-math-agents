"""Construct irreducible covering sets with prescribed largest modulus (Python 3.9+)."""
from math import lcm
import argparse


def factors(n):
    result = {}
    p = 2
    while p * p <= n:
        while n % p == 0:
            result[p] = result.get(p, 0) + 1
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1:
        result[n] = 1
    return result


def divisors(n):
    parts = factors(n)
    ds = [1]
    for p, a in parts.items():
        ds = [d * p**j for d in ds for j in range(a + 1)]
    return sorted(ds)


def cost(n):
    return sum((p - 1) * a for p, a in factors(n).items())


def construct(m, auxiliary=None):
    if m < 2:
        raise ValueError("largest modulus must exceed one")
    parts = factors(m)
    q = max(parts)
    b = parts[q]
    h = m // q**b
    if h < q:
        return None
    w = lcm(h, *range(1, q)) if auxiliary is None else auxiliary
    assert w % h == 0 and all(p < q for p in factors(w))
    classes = {}

    def digit(p, j, value, multiplier):
        power = p**j
        modulus = power * multiplier
        # Zero on the multiplier and value*p^(j-1) on the prime power.
        x = (value * (power // p) * pow(multiplier, -1, power)) % power
        assert modulus not in classes and 1 < modulus <= m
        classes[modulus] = x * multiplier

    prefix = 1
    for p, a in sorted(factors(w).items()):
        for j in range(1, a + 1):
            ds = [d for d in divisors(prefix) if d * p**j <= m]
            assert len(ds) >= p - 1
            for value, d in enumerate(ds[:p - 1], 1):
                digit(p, j, value, d)
        prefix *= p**a
    if auxiliary is None:
        last = [*range(1, q), h]
    else:
        ds = [d for d in divisors(w) if d <= h]
        # Include h. For optimal w every q choices including h have lcm w.
        last = [*ds[:q - 1], h]
    assert len(set(last)) == q and lcm(*last) == w
    for j in range(1, b):
        for value, d in enumerate(last[:-1], 1):
            digit(q, j, value, d)
    for value, d in enumerate(last):
        digit(q, b, value, d)
    return classes


def finite_bound(h, q):
    """Minimum auxiliary cost from the top q-adic digit, all subsets implicit."""
    universe = lcm(*(d for d in range(1, h + 1) if d % q))
    admissible = [w for w in divisors(universe) if w % h == 0 and
                  sum(w % d == 0 for d in range(1, h + 1)) >= q]
    return min((cost(w), w) for w in admissible)


def subset_bound(h, q):
    # Alternate calculation by adjoining distinct candidate multipliers.
    # Each set stores lcms of exactly i inputs together with the required h.
    states = [{h}] + [set() for _ in range(q)]
    for d in range(1, h + 1):
        if d % q:
            for i in range(q, 0, -1):
                states[i].update(lcm(v, d) for v in states[i - 1])
    return min((cost(w), w) for w in states[q])


def verify(classes, m, exhaustive_limit):
    mods = sorted(classes)
    period = lcm(*mods)
    assert max(mods) == m and len(mods) == 1 + cost(period)
    # Check the obstruction to every reassigned proper subset.
    for d in divisors(period):
        if d < period:
            assert sum(d % n == 0 for n in mods) <= cost(d)
    if period > exhaustive_limit:
        return False
    counts = bytearray(period)
    for n, r in classes.items():
        for x in range(r, period, n):
            counts[x] += 1
    assert min(counts) > 0
    assert all(any(counts[x] == 1 for x in range(r, period, n))
               for n, r in classes.items())
    return True


def checks():
    yes = direct = 0
    for m in range(2, 501):
        cs = construct(m)
        # Independently characterize the impossible integers by h*q^b, h<q.
        excluded = any(m % power == 0 and m // power < p
                       for p in range(2, m + 1) if factors(p) == {p: 1}
                       for b in range(1, m.bit_length() + 1)
                       if (power := p**b) <= m)
        assert (cs is None) == excluded
        if cs is not None:
            yes += 1
            direct += verify(cs, m, 100000)
    print(f"2..500: {yes} constructors, {direct} complete-period scans")
    for h in (9, 27):
        for q in range(5, h):
            if factors(q) != {q: 1}:
                continue
            c, w = finite_bound(h, q)
            assert (c, w) == subset_bound(h, q)
            for b in (1, 2):
                m = h * q**b
                cs = construct(m, w)
                assert len(cs) == 1 + c + b * (q - 1)
                verify(cs, m, 150000)
            print(f"h={h}, q={q}: W={w}, cost={c}")
    cs = construct(315, 90)
    assert len(cs) == 16 and verify(cs, 315, 630)
    print("315 certificate (modulus, residue)", sorted(cs.items()))
    cs = construct(175, 150)
    assert finite_bound(25, 7) == (10, 100)
    assert len([d for d in divisors(700) if 1 < d <= 175]) == 15
    assert len(cs) == 18 and verify(cs, 175, 1050)
    for a in range(1, 13):
        h = 5**a
        for t in (6, 8):
            assert sum(d <= h for d in divisors(t * h)) == 4 * a
        if a <= 8:
            for q in range(7, 4 * a + 1):
                if factors(q) != {q: 1}:
                    continue
                for b in (1, 2, 3):
                    m = h * q**b
                    cs = construct(m, 6 * h)
                    assert len(cs) == 4 + 4 * a + b * (q - 1)
                    verify(cs, m, 150000)
    print("5^a q^b family: auxiliary divisor counts through a=12, witnesses through a=8, b=3")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("maximum", nargs="?", type=int)
    parser.add_argument("--auxiliary", type=int,
                        help="use a specified compatible W, e.g. 90 for maximum 315")
    args = parser.parse_args()
    if args.maximum is None:
        checks()
    else:
        answer = construct(args.maximum, args.auxiliary)
        print("impossible" if answer is None else sorted(answer.items()))
