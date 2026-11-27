"""Check finite CRT covers, their translated prime progressions, and the gain truncation."""
from collections import Counter
from fractions import Fraction
from functools import cache
from math import floor, gcd, isqrt, log1p, prod, sqrt


@cache
def factors(n):
    value = n
    out = {}
    divisor = 2
    while divisor * divisor <= value:
        while value % divisor == 0:
            out[divisor] = out.get(divisor, 0) + 1
            value //= divisor
        divisor = 3 if divisor == 2 else divisor + 2
    if value > 1:
        out[value] = 1
    return out


@cache
def prime(n):
    return n > 1 and factors(n) == {n: 1}


def cover(y, z, u, length):
    primes = [p for p in range(y, u + 1) if prime(p)]
    remaining = set(range(1, length + 1))
    residues = {}
    for p in primes:
        if z < p and 2 * p <= u:
            residues[p] = 0
            remaining = {i for i in remaining if i % p}
    for p in primes:
        if p <= z:
            sizes = Counter(i % p for i in remaining)
            residue = max(range(p), key=lambda a: sizes[a])
            residues[p] = residue
            remaining = {i for i in remaining if i % p != residue}
    for p in primes:
        if 2 * p > u and p not in residues:
            residue = min(remaining) % p if remaining else 0
            residues[p] = residue
            remaining = {i for i in remaining if i % p != residue}
    assert not remaining
    modulus = prod(primes)
    start = sum((-r) * (modulus // p) * pow(modulus // p, -1, p) for p, r in residues.items()) % modulus
    assert all(gcd(start + i, modulus) > 1 for i in range(1, length + 1))
    return modulus, start


def local_gain(m):
    gain = 0.0
    for p, exponent in factors(m).items():
        power = p
        previous = 0
        while power < m:
            previous += (m - 1) // power
            power *= p
        gain += log1p(exponent / (1 + previous))
    return gain


def phi(n):
    result = n
    for p in factors(n):
        result -= result // p
    return result


def check_lifts(y, z, u, h, start_multiple):
    modulus, start = cover(y, z, u, h)
    width = modulus * 480 + 37
    x = start_multiple * width + 31
    cap = 2 * h + 5
    assert cap <= isqrt(x) and x // cap > u
    j0 = (x - start + modulus - 1) // modulus
    j1 = (x + width - start) // modulus
    assert abs(j1 - j0 + 1 - width / modulus) <= 1
    direct = Counter()
    for j in range(j0, j1 + 1):
        n = j * modulus + start
        gain = 0.0
        truncated = 0.0
        for i in range(1, h + 1):
            m = n + i
            gain += local_gain(m)
            for s in range(1, cap + 1):
                q, r = divmod(m, s)
                if r == 0 and prime(q):
                    direct[s] += 1
                    truncated += log1p(1 / s)
                    assert s >= y and gcd(s, modulus) > 1
        assert -1e-11 <= gain - truncated <= h * (log1p(1 / (cap + 1)) + 2 / sqrt(n)) + 1e-11

    for s in range(1, cap + 1):
        d = gcd(modulus, s)
        reduced = s // d
        offsets = [i for i in range(1, h + 1) if (start + i) % d == 0]
        assert len(offsets) <= h // d + 1
        count = 0
        for i in offsets:
            j_class = -((start + i) // d) * pow(modulus // d, -1, reduced) % reduced
            first_j = j0 + (j_class - j0) % reduced
            if first_j > j1:
                continue
            first_p = (first_j * modulus + start + i) // s
            last_p = (j1 * modulus + start + i) // s
            count += sum(prime(p) for p in range(first_p, last_p + 1, modulus // d))
        assert count == direct[s]
    # The divisor-sum identity behind the translated mean bound is exact.
    left = sum(Fraction(gcd(s, modulus), s * s) for s in range(1, cap + 1))
    right = sum(Fraction(phi(d), d * d * k * k)
                for d in range(1, cap + 1) if modulus % d == 0
                for k in range(1, cap // d + 1))
    assert left == right
    return j1 - j0 + 1, sum(direct.values())


if __name__ == "__main__":
    totals = [0, 0]
    for y, z, u, h in [(2, 3, 7, 6), (2, 3, 13, 9), (3, 5, 13, 6), (3, 3, 11, 5)]:
        for multiplier in [1, 11]:
            starts, hits = check_lifts(y, z, u, h, multiplier)
            totals[0] += starts
            totals[1] += hits
    print(f"Checked 8 translated covers, {totals[0]} CRT lifts, and {totals[1]} prime/cofactor hits.")
