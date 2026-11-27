"""Rational upper sums for equation (19) of Erdős–Graham–Ivić–Pomerance.

Reference: P. Erdős, S. W. Graham, A. Ivić and C. Pomerance, "On the
number of divisors of n!", pp. 11–12, equation (19) and the definition
of I(c) in the proof of Lemma 3. https://math.dartmouth.edu/~carlp/factorial.pdf

For u in a band assigned the exponent pair (k,l), its integrand is
u theta(u,k,l) = 2(1+k-l)u / (c(1+k)-k+(k-l)u). The switches are
alpha=(1+17c)/18 and beta=(1+5c)/6, and the endpoint is 1-c+delta.

This checks the scalar inequality c + I(c) < 1 for the three indicated
exponent pairs. A formal application at the new c requires the analytic
bound (19) and the sieve/reduction with the changed endpoints.
"""
from fractions import Fraction as F

DELTA = F(1, 10000)
GRID = 2048
SCALE = 10**12


def upper_integral(c):
    alpha, beta = (1 + 17 * c) / 18, (1 + 5 * c) / 6
    end = 1 - c + DELTA
    assert 0 < c < alpha < beta < end < (1 + c) / 2
    mass = c
    for lo, hi, k, ell in [
        (c, alpha, F(1, 14), F(11, 14)),
        (alpha, beta, F(1, 6), F(2, 3)),
        (beta, end, F(1, 2), F(1, 2)),
    ]:
        a, b = c * (1 + k) - k, k - ell
        # d/du [u/(a+bu)] = a/(a+bu)^2, so right endpoints give upper sums.
        assert a > 0 and min(a + b * lo, a + b * hi) > 0
        step = (hi - lo) / GRID
        for j in range(1, GRID + 1):
            u = lo + j * step
            integrand = 2 * (1 + k - ell) * u / (a + b * u)
            units = -(-integrand.numerator * SCALE // integrand.denominator)
            mass += step * F(units, SCALE)
    return mass


if __name__ == "__main__":
    for c in [F(4, 9), F(11101, 25000)]:
        bound = upper_integral(c)
        assert bound < 1
        print(f"c = {c}, c + I(c) <= {bound} ({float(bound):.10f})")
