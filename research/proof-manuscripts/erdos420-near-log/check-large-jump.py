"""Finite checks for the LCM seed and the cofactor certificates in large-jump.md.

The CRT in these finite examples certifies divisibility only. The bound on
the size of the translate in the theorem comes from the cited analytic lemma.
"""
from math import gcd, isqrt, lcm, prod


def primes_up_to(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[:2] = bytes(2)
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((n - p*p)//p + 1)
    return [p for p in range(2, n + 1) if sieve[p]]


def factorization(n):
    factors = {}
    for p in primes_up_to(isqrt(n)):
        while n % p == 0:
            factors[p] = factors.get(p, 0) + 1
            n //= p
    if n > 1:
        factors[n] = 1
    return factors


def verify_seed(x, h, w):
    modulus = lcm(*range(1, x + 1))
    bad = {m for m in range(1, 3*w + 1) if modulus % m}
    via_powers = {m for m in range(1, 3*w + 1)
                  if any(p**e > x for p, e in factorization(m).items())}
    assert bad == via_powers
    failures = {a: [i for i in range(1, h + 1) if a + i in bad]
                for a in range(w, 2*w + 1)}
    assert sum(map(len, failures.values())) <= h * len(bad)
    a = min(failures, key=lambda offset: len(failures[offset]))
    exceptions = failures[a]
    candidates = [p for p in primes_up_to(200*w) if p > max(x, h, 3*w)]
    assert len(candidates) >= len(exceptions)
    certificates = {i: a + i for i in range(1, h + 1) if i not in exceptions}
    # A translated block can start anywhere. Its first member in the seed
    # residue class is the base of the linear forms.
    base = a + modulus * (max(candidates)**2 + 1)
    t, period = 0, 1
    for i, p in zip(exceptions, candidates):
        assert gcd(modulus, p) == 1
        residues = {(-(base+j) * pow(modulus, -1, p)) % p for j in exceptions}
        assert len(residues) == len(exceptions)
        root = -(base+i) * pow(modulus, -1, p) % p
        t += period * ((root - t) * pow(period, -1, p) % p)
        period *= p
        certificates[i] = p
    n = base + modulus*t
    for i, d in certificates.items():
        assert w < d and d*d < n+i and (n+i) % d == 0
    return len(certificates), len(exceptions)


def verify_factorial_steps(limit):
    # Check exp(G_m) exactly and use
    # (1+v_p(m)/(1+v_p((m-1)!))) <= 1+p*v_p(m)/m as a rational inequality.
    exponents = {}
    checked = 0
    for m in range(2, limit+1):
        factors = factorization(m)
        assert prod(p**e for p, e in factors.items()) == m
        for p, e in factors.items():
            previous = exponents.get(p, 0)
            assert m <= p*(1+previous)
            if p*p > m:
                s = m//p
                assert previous == s-1 and e == 1
                for d in range(2, isqrt(m)+1):
                    if m % d == 0:
                        assert s % d == 0
                        checked += 1
            exponents[p] = previous+e
        if m >= 16:
            small_sum = sum(p*e for p, e in factors.items() if p*p <= m)
            assert small_sum**2 <= 4*m
    return checked


if __name__ == '__main__':
    counts = [verify_seed(x, h, w) for x, h, w in
              [(x, 2*x, 5*x) for x in range(8, 61, 4)]]
    print(f'{len(counts)} LCM seeds, {sum(a for a, _ in counts)} offsets, '
          f'{sum(b for _, b in counts)} exceptional-offset CRT certificates')
    print(f'{verify_factorial_steps(12000)} large-prime cofactor divisibilities; '
          'factorial-step inequalities checked through 12000')
