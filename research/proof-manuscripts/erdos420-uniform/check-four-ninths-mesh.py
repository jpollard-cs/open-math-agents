"""Check all 48 sieve levels, count allowances and the weighted prime budget exactly."""
from fractions import Fraction as F

c, d = F(4, 9), F(5, 9) + F(1, 10000)
knots = [c, F(77, 162), F(29, 54), d]
edges = [lo + j * (hi - lo) / 16 for lo, hi in zip(knots, knots[1:]) for j in range(16)] + [d]
mass = c
margins, savings = [], []
for j, (a, b) in enumerate(zip(edges, edges[1:])):
    lower = F(17, 24) - 5*b/4
    middle = F(19, 54) - b/2
    target = 1/lower if j < 16 else 1/middle if j < 32 else F(12)
    if j < 16:
        p, q, s, g = F(1, 15), F(2, 3), F(11, 15), lower - F(1, 10**9)
    elif j < 31:
        p, q, s, g = F(1, 7), F(3, 7), F(4, 7), middle - F(1, 10**9)
    else:
        p, q, s, g = F(1, 3), F(0), F(1, 3), F(1, 12) - F(1, 10**6)
    assert 0 < g <= 1 and 2*g < a
    cap = (b-a)*target + F(1, 10**6)
    margins.append(cap - (b-a)/g)
    savings.append(c - max(c+2*g-a, p+b*q+2*g*(1-s), 2*b-1))
    mass += b*cap
assert min(savings) > 0 and min(margins) > 0
assert mass < F(2499, 2500)
print(f"Passed all {len(savings)} bands. Smallest exponent saving = {min(savings)}.")
print(f"Smallest count allowance margin = {min(margins)}.")
print(f"Weighted mesh including 4/9 = {float(mass):.12f} < 2499/2500.")
