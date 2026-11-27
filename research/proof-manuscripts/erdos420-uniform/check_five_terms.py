"""Independently clip the original five exponent inequalities on each u strip.
No formulas for the simplified lower/upper endpoints are used in this check.
"""
from fractions import Fraction as Q
from reference_pairs import exponent_pairs
C=Q(2177,5000)
B=1-C+Q(1,100000)
MARGIN=Q(1,10**6)
FOURIER_SLACK=Q(1,10**8)
C0=C-Q(1,10**7)


def five_terms(u,a,flip):
    r=u-C+FOURIER_SLACK
    outside,inner=(a,u-a) if flip else (u-a,a)
    product=inner+r
    phase=1+r-u
    return ((13*product+9*outside+phase)/14,
            product+2*outside/3,
            product+13*outside/12-phase/4,
            3*product/4+outside,
            3*product/4+outside/2+phase/4)


def allowed(lo,hi,flip):
    # Each affine inequality in a must hold at both endpoints of the u interval.
    lower,upper=Q(0),lo-MARGIN
    for u in (lo,hi):
        at_zero=five_terms(u,Q(0),flip)
        at_one=five_terms(u,Q(1),flip)
        for intercept,last in zip(at_zero,at_one):
            slope=last-intercept
            if slope>0: upper=min(upper,(u-MARGIN-intercept)/slope)
            elif slope<0: lower=max(lower,(u-MARGIN-intercept)/slope)
            else: assert intercept<=u-MARGIN
    return lower,upper


def main():
    pairs=exponent_pairs()
    pieces=2048
    width=(B-C)/pieces
    bound=C
    for i in range(pieces):
        lo=C+i*width
        hi=lo+width
        pair_level=max((C0*(1+k)-k+(k-l)*hi)/(1+k-l) for k,l in pairs)
        allowable=[(Q(0),min(pair_level,lo-MARGIN))]
        allowable.extend(allowed(lo,hi,flip) for flip in (True,False))
        level=Q(0)
        for a,b in sorted(allowable):
            if a<=level and b>level:level=b
        upper=2*hi/level
        unit=10**10
        bound+=width*Q(-(-unit*upper.numerator//upper.denominator),unit)
    assert bound<Q(9996,10000)
    print(f'{pieces} independently clipped u-intervals; direct five-term bound {bound} < 0.9996.')
    print('Decimal display:',float(bound))

if __name__=='__main__':main()
