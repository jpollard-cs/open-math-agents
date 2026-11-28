"""Check the finite tail inequality on certified exact-size constructions.

Run beside reciprocal.py, or set PYTHONPATH to its directory.
The limiting theorem is proved in critical-cap.md.
"""
from fractions import Fraction
from math import isqrt
from collections import Counter
from sys import argv
from reciprocal import check, factors, make


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((n - p*p) // p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def first_threshold(k):
    budget = 1
    u = 1
    while budget < k:
        u += 1
        powers = factors(u)
        if len(powers) == 1:
            budget += next(iter(powers)) - 1
    return u


def run(k):
    data = make(k)
    maximum, _ = check(data, k)
    moduli = {n for n, _ in data}
    first = Counter()
    for n in moduli - {maximum}:
        powers = factors(n)
        p = max(powers)
        if powers[p] == 1:
            first[p] += 1
    primes = primes_upto(isqrt(maximum))
    assert set(first) <= set(primes)
    # Drop a possible excess terminal entry to get a legitimate partial placement.
    deficit = sum(p - 1 - min(p - 1, first[p]) for p in primes)
    u = first_threshold(k)
    model_primes = primes_upto(u)
    ideal = {p * d for p in model_primes for d in range(1, p)}
    assert len(ideal) == sum(p - 1 for p in model_primes)
    for numerator in range(1, 32):
        s = Fraction(numerator, 32)
        def model_tail(scale, ps):
            return sum(max(0, p - 1 - numerator * scale // (32 * p)) for p in ps)
        ideal_tail = sum(n * 32 > numerator * u*u for n in ideal)
        assert ideal_tail == model_tail(u*u, model_primes)
        actual_tail = sum(n * 32 > numerator * maximum for n in moduli)
        assert actual_tail >= model_tail(maximum, primes) - deficit, (k, s)
    half = sum(2*n > maximum for n in moduli)
    mean = sum(moduli) / (k * maximum)
    print(f'{k:7d} {maximum:9d} {u:5d} {len(ideal ^ moduli):7d} {half/k:12.6f} {mean:10.6f}')


if __name__ == '__main__':
    print('      k         M     u   symdiff   above_half       mean')
    for size in map(int, argv[1:] or (100, 1000, 10000, 100000)):
        run(size)
