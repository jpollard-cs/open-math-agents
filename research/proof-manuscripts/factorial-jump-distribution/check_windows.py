"""Exact identities and a numerical example for moving factorial endpoints."""
from fractions import Fraction
from math import isqrt, log
from itertools import accumulate


def one_step_ratios(limit):
    """Use the prime factors of the entering integer only."""
    least = list(range(limit + 1))
    for p in range(2, isqrt(limit) + 1):
        if least[p] == p:
            for j in range(p*p, limit + 1, p):
                if least[j] == j:
                    least[j] = p
    values = [Fraction(1)] * (limit + 1)
    for m in range(2, limit + 1):
        a = m
        while a > 1:
            p = least[a]
            count = 0
            while a % p == 0:
                a //= p
                count += 1
            old, term = 0, (m-1)//p
            while term:
                old += term
                term //= p
            values[m] *= Fraction(old + count + 1, old + 1)
    return values


def divisor_count_factorial(n):
    count = 1
    for p in range(2, n+1):
        if any(p % d == 0 for d in range(2,isqrt(p)+1)):
            continue
        exponent = 0
        power = p
        while power <= n:
            exponent += n//power
            power *= p
        count *= exponent + 1
    return count


def exact_checks():
    steps = one_step_ratios(400)
    prefix = list(accumulate(steps, lambda a,b: a*b))
    independent = [divisor_count_factorial(n) for n in range(401)]
    assert prefix == independent
    # Include large abrupt changes, fixed, and staircase windows.
    heights = [lambda n: 7, lambda n: isqrt(n), lambda n: (n//17)*3+1,
               lambda n: 9 if n < 85 else 120, lambda n: n//2+1]
    count = 0
    for h in heights:
        for n in range(9,180):
            for s in range(1,min(8,h(n))+1):
                log_ratio = Fraction(independent[n+s+h(n+s)]*independent[n],
                                     independent[n+s]*independent[n+h(n)])
                outgoing = prefix[n+s]/prefix[n]
                regular = prefix[n+h(n)+s]/prefix[n+h(n)]
                extra = prefix[n+s+h(n+s)]/prefix[n+s+h(n)]
                assert regular*extra/outgoing == log_ratio
                assert h(n+s) >= h(n)
                count += 1
    print(f"{len(prefix)} independent factorial divisor counts and {count} exact moving-window comparisons passed.")


def finite_example():
    # Avoid factorials of very large integers by adding log prime factors.
    X = 100000
    steps = list(map(log,one_step_ratios(2*X+150)))
    partial = list(accumulate(steps))
    def height(n):
        return int(log(n))
    for lag in (1,3,6):
        changes = []
        for n in range(X, 2*X):
            # Cancellation here involves only moderate logs. Exact tests above use Fraction.
            outgoing = partial[n+lag]-partial[n]
            incoming = partial[n+lag+height(n+lag)]-partial[n+height(n)]
            changes.append(incoming-outgoing)
        unit = log(X)/(lag*X)
        up = sum(x > log(1.6) for x in changes)
        down = sum(x < -log(1.6) for x in changes)
        print(f"X={X}, lag={lag}: scaled up {up*unit:.5f}, down {down*unit:.5f}, absolute variation {sum(map(abs,changes))*unit:.5f}.")


if __name__ == "__main__":
    exact_checks()
    finite_example()
