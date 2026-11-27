"""Exact integer checks for the retained-window divisor inequalities."""
from collections import Counter
from math import prod


def factor(m):
    ans = Counter()
    d = 2
    while d*d <= m:
        while m % d == 0:
            ans[d] += 1
            m //= d
        d += 1
    if m > 1:
        ans[m] = 1
    return ans


def tau(exponents):
    return prod(e+1 for e in exponents.values())


def checks():
    fs = [factor(m) for m in range(1, 110)]
    steps = 0
    for a in fs[:36]:
        for multiple in fs[:36]:
            b = a + multiple
            for c in fs[:36]:
                assert tau(b+c)*tau(a) <= tau(a+c)*tau(b)
                steps += 1

    windows = 0
    fac = Counter()
    for n in range(1, 101):
        fac.update(fs[n-1])
        h = min(n, 8)
        rows = fs[n:n+h]
        for mask in range(1 << h):
            end = fac.copy()
            for i, row in enumerate(rows):
                if mask & (1 << i):
                    end.update(row)
            for B in sorted({0, n//4, n//2, n}):
                good = sum(bool(mask & (1 << i)) and max(row) > B
                           for i, row in enumerate(rows))
                assert tau(end)*(8*n)**good >= tau(fac)*(8*n+B)**good
                windows += 1
    print(f"{steps} diminishing-return comparisons and {windows} retained-window comparisons passed.")


if __name__ == "__main__":
    checks()
