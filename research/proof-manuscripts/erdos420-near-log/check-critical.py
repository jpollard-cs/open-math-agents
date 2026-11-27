"""Independent exact checks for the cofactor increments and singular-series averaging."""
from fractions import Fraction
from itertools import product
from math import isqrt, lcm, prod


def primes_to(bound):
    sieve = bytearray([1]) * (bound + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(bound) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes(1 + (bound - p*p)//p)
    return [p for p in range(2, bound + 1) if sieve[p]]


def factorial_valuation(m, p):
    val = 0
    while m:
        m //= p
        val += m
    return val


def exact_divisor_counts(limit, primes):
    return [prod(1 + factorial_valuation(m, p) for p in primes if p <= m)
            for m in range(limit + 1)]


def check_gain():
    size, lengths = 750, (1, 2, 3, 4, 6, 9, 12)
    primes = primes_to(size + max(lengths))
    ds = exact_divisor_counts(size + max(lengths), primes)
    prime_set = set(primes)
    cases = threshold_cases = 0
    for n in range(16, size + 1):
        for h in lengths:
            full = Fraction(ds[n+h], ds[n])
            for Q in (1, 2, 3, 4):
                truncated = Fraction(1)
                reconstructed = Fraction(1)
                for m in range(n+1, n+h+1):
                    hits = [s for s in range(1, Q+1) if m % s == 0 and m//s in prime_set]
                    assert len(hits) <= 1
                    if hits:
                        s = hits[0]
                        p = m//s
                        assert p*p > m and factorial_valuation(m-1, p) == s-1
                        truncated *= Fraction(s+1, s)
                    for p in primes:
                        if p > m:
                            break
                        if m % p == 0:
                            reconstructed *= Fraction(1 + factorial_valuation(m, p),
                                                      1 + factorial_valuation(m-1, p))
                assert full == reconstructed and truncated <= full
                cases += 1
            for m0 in (1, 2, 3):
                target = Fraction(m0+1, m0)
                small_cofactor_hit = any(m % s == 0 and m//s in prime_set
                                         for m in range(n+1, n+h+1) for s in range(1, m0+1))
                if small_cofactor_hit:
                    assert full >= target
                threshold_cases += 1
    return cases, threshold_cases


def check_local_means():
    cases = 0
    for labels in ((1, 2), (2, 3), (2, 2, 3), (2, 3, 5), (1, 4, 6)):
        L = lcm(*labels)
        slopes = tuple(L//s for s in labels)
        k = len(slopes)
        for p in (2, 3, 5, 7, 11):
            allowed = sum(all((a*m+b) % p for a, b in zip(slopes, shifts))
                          for shifts in product(range(p), repeat=k) for m in range(p))
            assert allowed == p*(p-1)**k
            cases += 1
    return cases


if __name__ == '__main__':
    counts, thresholds = check_gain()
    print(f'{counts} exact factorial/cofactor checks, {thresholds} threshold implications')
    print(f'{check_local_means()} exact local-factor identities')
