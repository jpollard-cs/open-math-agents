"""Finite checks for the reciprocal sawtooth estimate and its Fourier transfer.

Run with Python 3 and NumPy. The two constants are adjustable. All large
sawtooth comparisons use rigorous rational enclosures; only the cyclic
Fourier checks below use floating point. These tests are not uniform proofs.
"""

from fractions import Fraction as Q
from math import ceil, floor, lcm
from random import Random

import numpy as np

CUBE = 280
INVERSE = 1340


def within_bound(amount, x, t, u):
    """Compare to CUBE*(x/t)^(1/3)+INVERSE*u^2/(x*t) exactly."""
    excess = Q(amount) - Q(INVERSE) * u**2 / (x * t)
    return excess <= 0 or t * excess**3 <= x * CUBE**3


def indices(t, u, v):
    return range(floor(Q(u) / t) + 1, floor(Q(v) / t) + 1)


def saw_exact(x, t, u, v):
    return sum((Q(x % (t*j), t*j) - Q(1, 2) for j in indices(t, u, v)), Q(0))


def saw_enclosure(x, t, u, v):
    """Enclose R by rounding each centered sawtooth down on a binary grid."""
    js = indices(t, u, v)
    scale = 1 << 30
    chunk = 1 << 18
    assert x < 2**63 and (js.stop * t) * scale < 2**63
    assert chunk * scale < 2**63
    total = 0
    for start in range(js.start, js.stop, chunk):
        m = t * np.arange(start, min(start + chunk, js.stop), dtype=np.int64)
        total += int(np.sum(((x % m) * scale) // m - scale // 2, dtype=np.int64))
    return Q(total, scale), Q(total + len(js), scale)


def check_remainders():
    rng = Random(420)
    count = 0
    for case in range(750):
        t = rng.randint(1, 24)
        u = t + Q(rng.randint(0, 240), 4)
        v = u + Q(rng.randint(0, floor(8*u)), 4)
        js = indices(t, u, v)
        x = rng.choice([1, 10**20 + 39, rng.randint(1, 10**12)])
        if case % 11 == 0:
            x = lcm(*(t*j for j in js))
        observed = saw_exact(x, t, u, v)
        assert within_bound(abs(observed), x, t, u)
        if x < 2**63:
            lo, hi = saw_enclosure(x, t, u, v)
            assert lo <= observed <= hi
        count += 1
    assert saw_exact(60, 3, Q(3), Q(3)) == 0
    assert saw_exact(60, 3, Q(3), Q(6)) == -Q(1, 2)
    print(f"{count + 2} small exact tests passed, including integer hits and real endpoints.")

    # The triangle inequality alone fails for all three examples. Every
    # multiple in each block is evaluated. Only small arrays stay in memory.
    for t, u, v, x in [
        (1, Q(100_000_000), Q(300_000_000), 10**12),
        (3, Q(300_000_001, 1), Q(830_000_002, 1), 3*10**12 + 17),
        (7, Q(1_400_000_001, 2), Q(4_200_000_003, 2), 7*10**12 - 1),
    ]:
        assert t <= u <= v <= 3*u
        n = len(indices(t, u, v))
        assert not within_bound(Q(n, 2), x, t, u)
        lo, hi = saw_enclosure(x, t, u, v)
        assert within_bound(max(abs(lo), abs(hi)), x, t, u)
        # Widen the printed decimal endpoints outwards as well.
        left = floor(lo*10000) / 10000
        right = ceil(hi*10000) / 10000
        print(f"x={x}, t={t}, {n:,} terms, R in [{left:.4f}, {right:.4f}]")


def check_fourier():
    """Check all grid points including jumps, both frequency signs and the DC term."""
    rng = np.random.default_rng(420)
    cases = 0
    for q in (1, 2, 3, 8, 17, 36, 65, 96, 257, 512, 1024, 2048):
        a = np.arange(q)
        # s/(2q) is the grid sawtooth. Its forward FFT uses exp(-2πi j/q).
        s = 2*a - q
        coeff = np.fft.fft(s / (2*q)) / q
        j = a[1:]
        delta = np.expm1(-2j*np.pi*j/q)
        np.testing.assert_allclose(coeff[0], -0.5/q, atol=2e-15, rtol=0)
        np.testing.assert_allclose(coeff[1:], 1/(q*delta), atol=1e-12, rtol=1e-10)
        js = np.minimum(j, q-j)
        assert np.all(np.abs(coeff[1:]) <= 1/(4*js) + 1e-12)

        samples = [a, np.zeros(3*q, dtype=int), (a*a+3) % q,
                   rng.integers(q, size=2*q+1), np.array([0, 0, q-1]),
                   np.array([], dtype=int)]
        doubled = np.concatenate(([0], np.cumsum(np.tile(s, 2))))
        for H in (h for h in range(1, q+1) if q % h == 0):
            L = q//H
            # One-sided smoothing, multiplied by 2qL so both tests are exact.
            plus = doubled[a+L] - doubled[a]
            b = (a-L+1) % q
            minus = doubled[b+L] - doubled[b]
            assert np.all(plus-L*(L-1) <= L*s)
            assert np.all(L*s <= minus+L*(L-1))
            box = np.abs(np.fft.fft((a < L).astype(float))) / L
            assert np.all(box[1:] <= np.minimum(1, q/(2*L*js)) + 1e-12)
            for p in samples:
                n = len(p)
                spec = np.abs(np.fft.fft(np.bincount(p, minlength=q)))
                observed = abs(int(np.sum(s[p])) / (2*q))
                raw = n*(L-1)/(2*q) + np.sum(np.abs(coeff)*spec*box)
                tol = 1e-10 * (1+n)
                assert observed <= raw + tol
                for k in (1/14, 1/6, 1/2):
                    F = n/3
                    # Frequencies j >= q are covered by |S_j| <= n. Check all
                    # smaller frequencies to obtain a valid E for this sample.
                    E = max(n/q**k, np.max((spec[1:] - F/j) / j**k, initial=0))
                    budget = n/(2*H) + E*(1/k+1/(1-k))*H**k/2 + F
                    assert raw <= budget + tol
                    cases += 1
    print(f"{cases:,} finite Fourier transfer tests passed.")


if __name__ == "__main__":
    check_remainders()
    check_fourier()
