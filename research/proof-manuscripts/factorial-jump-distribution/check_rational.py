"""Exact checks of finite cofactor pairing in two rationally sampled factorial windows."""
from collections import Counter
from fractions import Fraction
from math import gcd, isqrt


def sieve(bound):
    largest = list(range(bound+1))
    primes = bytearray([1])*(bound+1)
    primes[0:2] = bytes(2)
    for p in range(2, isqrt(bound)+1):
        if primes[p]:
            primes[p*p::p] = bytes(len(primes[p*p::p]))
    for p in range(2,bound+1):
        if primes[p]:
            for n in range(p,bound+1,p):
                largest[n] = p
    pi = [0]
    for n in range(1,bound+1):
        pi.append(pi[-1]+primes[n])
    return largest,pi


def check():
    X,E = 4000,3
    largest,pi = sieve(2*X*13)
    slopes = 0
    align_count = 0
    integer_proxies = 0
    for A in range(2,14):
        for B in range(1,min(A,8)):
            if gcd(A,B)>1: continue
            slopes += 1
            entered = Counter()
            left = Counter()
            aligned = Counter()
            for m in range(X+1,2*X+1):
                outgoing_p = largest[m]
                outgoing = m//outgoing_p
                if outgoing <= B*E:
                    left[outgoing] += 1
                mark = None
                for t in range(A*(m-1)//B+1,A*m//B+1):
                    p = largest[t]
                    d = t//p
                    if d <= A*E:
                        entered[d] += 1
                        if d % A == 0:
                            assert B*t == A*m and d*B == outgoing*A and p == outgoing_p
                            assert mark is None
                            mark = d//A
                        elif outgoing <= B*E:
                            assert outgoing_p != p
                if outgoing <= B*E and outgoing % B == 0:
                    assert mark == outgoing//B
                if mark is not None:
                    aligned[mark] += 1
                    align_count += 1
                if B == 1:
                    # For integer slopes the mandatory t=Am term enforces
                    # the limiting lower constant for the P-plus proxy.
                    proxy = (1+Fraction(largest[A*m],A*m))/(1+Fraction(outgoing_p,m))
                    assert proxy >= Fraction(A+1,2*A)
                    integer_proxies += 1
            for d in range(1,A*E+1):
                assert entered[d] == pi[(A*2*X//B)//d]-pi[(A*X//B)//d]
            for d in range(1,B*E+1):
                assert left[d] == pi[2*X//d]-pi[X//d]
            assert all(aligned[e] == left[B*e] == entered[A*e] for e in range(1,E+1))
    print(f'{slopes} reduced slopes: entering/leaving counts match exact prime counts.')
    print(f'{align_count} alignments matched both coordinates and their largest prime.')
    print(f'{integer_proxies} integer-slope lower proxy bounds passed (integer arithmetic).')


if __name__ == '__main__':
    check()
