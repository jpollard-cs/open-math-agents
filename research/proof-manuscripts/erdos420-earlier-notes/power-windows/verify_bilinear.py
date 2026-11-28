"""Rational strip-by-strip certificate for the smoothed bilinear sieve."""
from fractions import Fraction as Q
from reference_pairs import exponent_pairs
C=Q(4354,10000)
DELTA=Q(1,100000)
GAP=Q(1,100000)
COLD=C-Q(1,10000000)
B=1-C+DELTA

def emit(strip_count=4096):
    step=(B-C)/strip_count
    total=Q(0)
    lines=[((COLD*(1+k)-k)/(1+k-l),(k-l)/(1+k-l)) for k,l in exponent_pairs()]
    used={'I':0,'II':0}
    count_edges=0
    for i in range(strip_count):
        left=C+i*step
        right=left+step
        previous=max(a+b*right for a,b in lines)
        level=previous
        lo=max(3*(right-C),13*right-9*C-3)
        hi=min((14*C-8*right-1)/4,3*C-2*right,4*C-right-1)
        options=[(lo+GAP,hi-GAP,'I'),(right-hi+GAP,left-lo-GAP,'II')]
        for _ in range(2):
            for start,end,tag in options:
                if start<=level<end:
                    level=end;used[tag]+=1
        level=min(level,left-GAP)
        assert level>0
        count_edges+=level>previous
        ratio=2*right/level
        rounded=-(-ratio.numerator*10**9//ratio.denominator)
        total+=Q(rounded,10**9)*step
    value=C+total
    print('C=',C,'delta=',DELTA,'mesh',strip_count,'enhanced strips',count_edges)
    print('Baker-Harman range extensions:',used)
    print('Strict-criterion exact upper bound',value,float(value))
    assert value<Q(1)
    return value

if __name__=='__main__':emit()
