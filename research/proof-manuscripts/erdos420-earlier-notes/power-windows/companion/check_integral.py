"""Second certificate: locate all intersections of the sieve-level lines exactly.
Integrate the selected rational functions with rational bounds for each logarithm.
"""
from fractions import Fraction as Q
from itertools import combinations
from verify_sieve import C, C_ERROR, RIGHT, exponent_pairs, log_interval


def upper_round(x, unit):
    return -((-x.numerator*unit)//x.denominator)


def main():
    lines=[]
    for k,ell in exponent_pairs():
        den=2*(1+k-ell)
        lines.append(((C_ERROR*(1+k)-k)/den,(ell-k)/den))
    cuts={C, RIGHT}
    for (a,b),(e,f) in combinations(lines,2):
        if b!=f:
            u=(a-e)/(b-f)
            if C<u<RIGHT: cuts.add(u)
    points=sorted(cuts)
    pieces=[]
    for l,r in zip(points,points[1:]):
        mid=(l+r)/2
        a,b=max(lines,key=lambda p:p[0]-p[1]*mid)
        assert a-b*r>0
        if pieces and pieces[-1][0:2]==(a,b):
            pieces[-1]=(a,b,pieces[-1][2],r)
        else:pieces.append((a,b,l,r))
    unit=10**15
    lower=upper=C
    for a,b,l,r in pieces:
        if b==0: lo=hi=(r*r-l*l)/(2*a)
        else:
            loglo,loghi=log_interval((a-b*l)/(a-b*r))
            lo,hi=(a*bound/(b*b)-(r-l)/b for bound in (loglo,loghi))
        lower+=Q(-upper_round(-lo,unit),unit)
        upper+=Q(upper_round(hi,unit),unit)
    assert Q(99992,100000)<lower<=upper<Q(99994,100000)
    print(f'{len(pieces)} affine-envelope regions after rational intersections.')
    print('Independent analytic integral enclosure:',lower,upper)
    print(f'{float(lower):.14f} to {float(upper):.14f} (decimal display).')

if __name__=='__main__':
    main()
