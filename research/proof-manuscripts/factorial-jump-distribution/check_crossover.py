"""Exact placement of simultaneous prime/cofactor rows near rational slopes."""
from fractions import Fraction
from math import gcd


def check():
    checks = 0
    for A in range(2,11):
        for B in range(1,A):
            if gcd(A,B)>1:
                continue
            alpha = Fraction(A,B)
            for X in (30,75,160):
                for c in (-3, Fraction(-1,10000),0,Fraction(1,10000),alpha/2,3*alpha/4,alpha,5*alpha/4,3):
                    beta = alpha + Fraction(c,X)
                    for m in range(X,2*X):
                        if m % B:
                            continue
                        t = A*(m//B)
                        actual = int(beta*(m-1)) < t <= int(beta*m)
                        predicted = c >= 0 and c*(m-1) < alpha*X
                        assert actual == predicted
                        checks += 1
    print(checks, 'microscopic alignment decisions agree with the overlap fraction.')


if __name__ == '__main__':
    check()
