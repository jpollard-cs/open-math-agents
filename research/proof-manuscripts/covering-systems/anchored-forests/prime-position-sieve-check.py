"""Exact finite tests for prime-position-sieve.md, using only Python's standard library."""
from fractions import Fraction
from functools import cache, reduce
from itertools import combinations, permutations
from math import ceil, gcd, lcm, prod


@cache
def harmonic(n):
    return sum((Fraction(1, j) for j in range(1, n + 1)), Fraction(0))


def example():
    rows = list(zip((2, 3, 4, 6, 5, 10, 15), (1, 0, 2, 2, 1, 2, 4)))
    for index, d in enumerate((3, 4, 5, 12, 15, 20, 30)):
        r = next(x for x in range(7*d) if x % 7 == index and x % d == 28 % d)
        rows.append((7*d, r))
    rows.append((20, 0))
    assert len(rows) == 15 and lcm(*(n for n, _ in rows)) == 420
    assert all(any(x % n == r for n, r in rows) for x in range(420))
    return rows


def check_positions():
    rows = example()
    tests = higher = large_lower_fibre = 0
    for order in sorted(set(permutations((2, 2, 3, 5, 7)))):
        for reserved, _ in rows:
            K = 1
            for p in order:
                old = [(n, r) for n, r in rows if n != reserved and K % n == 0]
                group = [n for n, _ in rows if n != reserved and (K*p) % n == 0 and K % n]
                power = p
                while K % power == 0:
                    power *= p
                previous = power // p
                for all_zero in (False, True):
                    holes = [x for x in range(K) if all(x % n != (0 if all_zero else r) for n, r in old)]
                    assert holes
                    u = len({x % previous for x in holes})
                    G = reduce(gcd, (x - holes[0] for x in holes), K)
                    trace = {n // power: len({x % (n//p) for x in holes}) for n in group}
                    aligned = sorted(c for c, t in trace.items() if t == 1)
                    assert len(aligned) < p
                    for s in sorted({0, len(aligned)}):
                        A, d = aligned[:s], p - s
                        B = sorted(set(trace) - set(A))
                        assert all(G % a == 0 for a in A)
                        W = sum(Fraction(1, c) for c in trace)
                        if B:
                            T = Fraction(min(trace[c] for c in B), u)
                            assert T >= 1 and len(B) < d * len(holes)
                            assert all(Fraction(c, gcd(c, G)) >= T for c in B)
                            excess = harmonic(ceil(T) + len(B) - 1) - harmonic(ceil(T) - 1)
                            assert W <= harmonic(p - 1) + excess
                            if W > harmonic(p - 1):
                                omitted = sum(Fraction(1,n) for n in range(1,p) if G % n)
                                assert omitted <= 1 + sum(Fraction(1,b) for b in B)
                        else:
                            assert W <= harmonic(p - 1)
                        tests += 1
                        higher += previous > 1
                        large_lower_fibre += u > 1
                K *= p
            assert K == 420
    return tests, higher, large_lower_fibre


def check_sieve():
    # Compare both Bonferroni truncations with exact, direct integer counts.
    primes = (2, 3, 5, 7, 11, 13, 17)
    tests = 0
    for k in range(1, len(primes)+1):
        for chosen in combinations(primes, k):
            for x in (17, 100, 1001):
                count = sum(all(n % p for p in chosen) for n in range(x, 2*x))
                trunc = x
                for i in range(1, k+1):
                    for subset in combinations(chosen, i):
                        v = prod(subset)
                        trunc += (-1)**i * ((2*x-1)//v - (x-1)//v)
                    assert (trunc <= count if i%2 else trunc >= count)
                    tests += 1
                assert trunc == count
    return tests


if __name__ == '__main__':
    print('position tests, higher positions, multiple old p-residues:', *check_positions())
    print('sieve truncation tests:', check_sieve())
