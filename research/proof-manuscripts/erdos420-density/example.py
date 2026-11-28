"""Exact factorial-divisor ratios near (3/2)^2, for a single starting integer."""
from fractions import Fraction
from math import factorial, prod

n = 7_972_317
partial = sum(Fraction(1, factorial(j)) for j in range(8))
assert Fraction(2718,1000) < partial < partial + Fraction(9, 8*factorial(8)) < Fraction(2719,1000)
assert Fraction(2719,1000)**15 < n < Fraction(2718,1000)**16


def factors(a):
    found = {}
    d = 2
    while d*d <= a:
        while a % d == 0:
            found[d] = found.get(d, 0)+1
            a //= d
        d += 1
    if a > 1:
        found[a] = 1
    return found


def legendre(m, p):
    total = 0
    while m:
        m //= p
        total += m
    return total


product = Fraction(1)
support = set()
for h in range(1, 16):
    row = factors(n+h)
    if h in (1, 5):
        assert row == {2: 1, (n+h)//2: 1}
    for prime, exponent in row.items():
        a = legendre(n+h-1, prime)
        product *= Fraction(a+1+exponent, a+1)
    support.update(row)
    independent = prod(Fraction(legendre(n+h,p)+1,legendre(n,p)+1) for p in support)
    assert product == independent
    if h >= 5:
        assert Fraction(225,100) < product < Fraction(227,100)
    if h in (5,15):
        print(f"h={h}, F={float(product):.10f}")
print("All eleven window lengths gave a ratio strictly between 2.25 and 2.27.")
