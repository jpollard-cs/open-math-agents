"""Exact upper Darboux certificate for the EGIP sieve, plus the ideal barrier."""
from fractions import Fraction as Q
from math import lcm

C = Q(4411, 10000)
DELTA = Q(1, 100000)
C_ERROR = C - Q(1, 10**7)
RIGHT = 1 - C + DELTA
N = 32768
SCALE = 10**9


def exponent_pairs():
    pairs = [
        (Q(13,84),Q(55,84)), (Q(4742,38463),Q(35731,51284)),
        (Q(18,199),Q(593,796)), (Q(2779,38033),Q(58699,76066)),
        (Q(89,1282),Q(997,1282)), (Q(9,217),Q(1461,1736)),
        (Q(10769,351096),Q(609317,702192)), (Q(89,3478),Q(15327,17390)),
    ]
    for m in range(6,17):
        pairs.append((Q(2,(m-1)**2*(m+2)), 1-Q(3*m-2,m*(m-1)*(m+2))))
    return sorted(set(pairs + [(ell-Q(1,2), k+Q(1,2)) for k,ell in pairs]))


def certify():
    step = (RIGHT-C)/N
    grid_denominator = lcm(C.denominator,step.denominator)
    start = int(C*grid_denominator)
    stride = int(step*grid_denominator)
    lines=[]
    for k,ell in exponent_pairs():
        divisor=2*(1+k-ell)
        intercept=(C_ERROR*(1+k)-k)/divisor
        slope=(k-ell)/divisor
        assert intercept>0 and slope<=0
        denominator=lcm(intercept.denominator,slope.denominator)
        # If u=j/grid_denominator then u/Phi(u)=j*d/(b+q*j).
        lines.append((int(intercept*denominator)*grid_denominator,int(slope*denominator),denominator))
    total=0
    for i in range(1,N+1):
        j=start+i*stride
        candidates=[]
        for b,q,d in lines:
            positive=b+q*j
            if positive>0:
                candidates.append((j*d*SCALE+positive-1)//positive)
        total+=min(candidates)
    bound=C+step*Q(total,SCALE)
    assert bound < Q(99996,100000)
    print(f'{len(lines)} valid pairs, {N} right-hand rectangles, upward rounding to 1/{SCALE}.')
    print('Exact upper bound:',bound)
    print('Upward decimal enclosure:',f'{-(-bound.numerator*10**10//bound.denominator)/10**10:.10f}')
    return bound


def log_interval(x):
    z=(x-1)/(x+1)
    assert 0<z<1
    terms=24
    lower=2*sum(z**(2*j+1)/(2*j+1) for j in range(terms))
    upper=lower+2*z**(2*terms+1)/((2*terms+1)*(1-z*z))
    return lower,upper


def ideal_barrier():
    lo,hi=Q(40980664,10**8),Q(40980665,10**8)
    for c,side in [(lo,'lower'),(hi,'upper')]:
        a,b=log_interval(c/(3*c-1))
        if side=='lower':
            assert 5*c-3+4*c*a>0
        else:
            assert 5*c-3+4*c*b<0
    print('Ideal equality has a unique root in (0.40980664, 0.40980665).')


if __name__=='__main__':
    certify()
    ideal_barrier()
