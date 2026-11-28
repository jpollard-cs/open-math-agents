"""Cross-check the exact exceptional-pair count and joint hole quantifiers."""
from itertools import combinations, product
from math import isqrt, lcm, prod


def primes_and_factors(cap):
    factors = [[] for _ in range(cap+1)]
    for p in range(2,cap+1):
        if not factors[p]:
            for n in range(p,cap+1,p):
                factors[n].append(p)
    return factors


def arithmetic():
    cases = 0
    multiplicities = 0
    for X in (*range(100,620,7), 1000, 3360, 10000, 32768, 67500):
        fs = primes_and_factors(X)
        P = [p for p in range(2,isqrt(X)+1) if fs[p] == [p]]
        for Y in range(2,isqrt(X)+1):
            if Y**3 < X:
                continue
            high = [p for p in P if p > Y]
            formula = sum(X//(p*q) for p,q in combinations(high,2))
            actual = sum(len(f)>=2 and f[-1]<=isqrt(X) and f[-2]>Y for f in fs)
            assert actual == formula
            for p,q in combinations(high,2):
                assert X//(p*q) <= X//((Y+1)**2)
            cases += 1
            multiplicities += actual
    return cases,multiplicities


def exact_cuts():
    count = equality = 0
    for D in ((2,3,4,6,12), (2,3,4,6,8,24), (2,3,4,6,9,18,36),
              (2,3,4,5,6,10,15,20,30)):
        X, period = max(D), lcm(*D)
        fs = primes_and_factors(X)
        masks = {n: {sum(1<<x for x in range(r,period,n)) for r in range(n)} for n in D}
        for reserved in D:
            for Y in range(1,isqrt(X)+1):
                groups = {}
                for n in D:
                    p = fs[n][-1]
                    if n == reserved or n%(p*p)==0 or any(s>Y for s in fs[n//p]):
                        continue
                    groups.setdefault(p,[]).append(n)
                # All complete batch choices are enumerated for these examples.
                assert all(len(rows)<2*q for q,rows in groups.items())
                choices = [[(q,b) for b in combinations(rows,q)] for q,rows in groups.items()
                           if len(rows)>=q]
                for grouping in product(*choices):
                    for band in {q.bit_length() for q,_ in grouping}:
                        batches = [(q,b) for q,b in grouping if q.bit_length()==band]
                        active = {n for _,b in batches for n in b}
                        covered = {0}
                        for n in set(D)-active-{reserved}:
                            covered = {a|b for a in covered for b in masks[n]}
                        guards = [lcm(*(n//q for n in b)) for q,b in batches]
                        for g in guards:
                            rest = g
                            for p in range(2,Y+1):
                                while rest % p == 0:
                                    rest //= p
                            assert rest == 1
                        for mask in covered:
                            visible = {tuple(x%g for g in guards) for x in range(period) if not mask>>x&1}
                            bs = [len({x[i] for x in visible}) for i in range(len(guards))]
                            lhs, rhs = prod(bs), len(visible)*prod(b-1 for b in bs)
                            assert all(b>=2 for b in bs) and lhs <= rhs
                            count += 1
                            equality += lhs == rhs
    return count,equality


if __name__ == '__main__':
    print('arithmetic cutoffs and counted multiples:', *arithmetic())
    print('trimmed complementary masks and product equalities:', *exact_cuts())
