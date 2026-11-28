"""Outward-rounded integer enclosures for the logarithmic coefficient at tau = 0."""
from array import array
from fractions import Fraction as Q

M = 100_000
D = 10**14


def ceildiv(a, b):
    return -(-a // b)


def bounds(delta):
    end = ceildiv(M * delta.denominator, delta.numerator)
    top = Q(M, 2) / delta
    integral_lo = integral_hi = 0
    # lo,hi enclose D*rho(i/M). J sums have units 1/(M*D).
    lo = array("q", [D]) * (M + 1)
    hi = array("q", [D]) * (M + 1)
    jlo = jhi = M * D
    for i in range(M, end):
        lo.append(max(0, lo[i] - ceildiv(hi[i-M], i)))
        hi.append(hi[i] - lo[i+1-M] // (i+1))
        if i < top:
            # On a final fractional cell bound the full cell from above only.
            if i+1 <= top:
                integral_lo += jlo // (i+1)
            integral_hi += ceildiv(jhi + hi[i], i)
        jlo += lo[i+1]
        jhi += hi[i]
    # J(1/delta) may end partway through the last cell.
    if Q(M) / delta != end:
        jlo -= lo[end]
    return (delta * Q(jlo + integral_lo, M*D),
            delta * Q(jhi + integral_hi, M*D))


if __name__ == "__main__":
    for d in [Q(12,100), Q(13,100), Q(13088,100000), Q(13091,100000)]:
        a,b = bounds(d)
        print(str(d), float(a), float(b))
        if d == Q(13,100):
            t = Q(1,1000)
            # log(50/13)<7/5 follows by summing the exponential series to degree 4.
            assert sum(Q(7,5)**j / __import__("math").factorial(j) for j in range(5)) > Q(50,13)
            assert b + t*Q(7,5) + t*t/(2*d) < Q(4997,10000)
        if d == Q(13088,100000):
            assert b < Q(1,2)
        if d == Q(13091,100000):
            assert a > Q(1,2)
