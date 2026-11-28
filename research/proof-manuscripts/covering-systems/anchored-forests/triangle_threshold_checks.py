"""Integer checks for the two numerical regimes and rational cost optimization."""
from fractions import Fraction as F
from math import isqrt, prod


def prime(n):
    return n >= 2 and all(n % j for j in range(2, isqrt(n) + 1))


def main():
    small = [n for n in range(2, 72) if prime(n)]
    assert len(small) == 20
    assert all(2**i >= p - 1 for i,p in enumerate(small))
    t = 2**len(small)
    for ps, yes in [((1050139,1050151,1050167),True),((1050331,1050337,1050349),False)]:
        assert all(map(prime, ps)) and ps[-1] <= 4*t
        a,b,c = [p-t for p in ps]
        if yes:
            assert c*(c-isqrt(t)) <= t
        else:
            d = 1 - F(t,a*a)
            margin = d*d+d-1
            assert margin/(3+margin) > F(t,a*b*c)
            assert t*(a+b+c+1) >= a*b*c
        print(prod(small), ps, 'positive' if yes else 'excluded')
    count = 0
    for j in range(39,91):
        b = F(j,100)
        x = max(F(0), (1-2*b)/(1-b))
        optimum = 1+b*x
        grid = [F(k,100) for k in range(j+1)]
        for u in grid:
            for v in grid:
                z=(1-u)*(1-v)
                if z <= b:
                    assert u+v+z >= optimum
                    count += 1
        assert (1-x)*(1-b)<=b
    print(count, 'feasible rational comparisons')
if __name__=='__main__':
    main()
