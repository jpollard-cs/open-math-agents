"""Exact checks for projected-holes.md. Run with Python 3 and the companion sieve checker."""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import cache
from itertools import permutations, product
from math import gcd, lcm
from pathlib import Path
from runpy import run_path


@cache
def divisors(n):
    return tuple(d for d in range(1, n + 1) if n % d == 0)


@cache
def harmonic(n):
    return sum((Fraction(1, d) for d in range(1, n + 1)), Fraction())


def small_example():
    moduli = (2, 3, 4, 6, 12)
    period = lcm(*moduli)
    def covers(rows):
        return all(any(x % n == r for n, r in rows) for x in range(period))

    for omit in moduli:
        others = tuple(n for n in moduli if n != omit)
        assert not any(covers(tuple(zip(others, assignment)))
                       for assignment in product(*(range(d) for d in others)))
    for assignment in product(*(range(d) for d in moduli)):
        rows = tuple(zip(moduli, assignment))
        if covers(rows):
            return rows
    raise AssertionError("period-12 example did not cover")


def check_position(K, p, old, new, assignments, tally):
    old_power = 1
    while K % (p * old_power) == 0:
        old_power *= p
    power = p * old_power
    cofactors = tuple(n // power for n in new)
    mass = sum((Fraction(1, c) for c in cofactors), Fraction())
    for residues in assignments:
        holes = [x for x in range(K) if all(x % n != r for n, r in zip(old, residues))]
        assert holes
        for g in divisors(K // old_power):
            b = len({x % g for x in holes})
            P = power * b
            groups = defaultdict(list)
            for c in cofactors:
                groups[c // gcd(c, g)].append(c)
            for v, cs in groups.items():
                # Count actual simultaneous row signatures on every lifted hole.
                pairs = {tuple((x + K * d) % (power * c) for c in cs)
                         for x in holes for d in range(p)}
                assert len(cs) < len(pairs) <= P * v
                assert all(c % v == 0 and (g * v) % c == 0 for c in cs)
                old_primes = [r for r in divisors(v) if len(divisors(r)) == 2]
                z = v
                for r in old_primes:
                    t = g
                    while t % r == 0:
                        z *= r
                        t //= r
                assert all(c % z == 0 for c in cs)
                tally["nonempty groups"] += 1
            clipped = sum((Fraction(1, max(P, c)) for v, cs in groups.items()
                           if v != 1 for c in cs), Fraction())
            assert mass <= harmonic(P - 1) + clipped
            tally["projected cuts"] += 1
            tally["cuts with multiple projected holes"] += b > 1


def check_cover(rows, factors, exhaustive, tally):
    for order in sorted(set(permutations(factors))):
        for reserve, _ in rows:
            K = 1
            for p in order:
                earlier = [(n, r) for n, r in rows if n != reserve and K % n == 0]
                old = [n for n, _ in earlier]
                new = [n for n, _ in rows if n != reserve and K % n and (p * K) % n == 0]
                choices = (product(*(range(n) for n in old)) if exhaustive else
                           {tuple(r for _, r in earlier), (0,) * len(old)})
                check_position(K, p, old, new, choices, tally)
                K *= p


def check_moments():
    # The divisibility second-moment estimate works for arbitrary nonnegative weights.
    primes = (2, 3, 5, 7)
    tests = 0
    for weights in ((1, 2, 3, 4), (7, 2, 5, 1)):
        for exponents in product(range(3), repeat=len(primes)):
            linear = sum(Fraction(w, r**a * (r - 1))
                         for r, a, w in zip(primes, exponents, weights))
            diagonal = sum(Fraction((r + 1) * w**2, r**a * (r - 1)**2)
                           for r, a, w in zip(primes, exponents, weights))
            squares = 0
            for n in range(1, 258):
                z = 0
                for r, a, w in zip(primes, exponents, weights):
                    t = n
                    while t % r == 0:
                        t //= r
                        a -= 1
                        if a < 0:
                            z += w
                squares += z**2
                if n in (7, 32, 97, 257):
                    assert Fraction(squares, n) <= linear**2 + diagonal
                    tests += 1
    return tests


if __name__ == "__main__":
    tally = Counter()
    check_cover(small_example(), (2, 2, 3), True, tally)
    companion = Path(__file__).with_name("prime-position-sieve-check.py")
    check_cover(run_path(str(companion))["example"](), (2, 2, 3, 5, 7), False, tally)
    for key, count in sorted(tally.items()):
        print(f"{key}: {count}")
    print("rational second-moment checks:", check_moments())
