"""Construct a covering set of prescribed cardinality, and check its certificate."""
from bisect import bisect_right
from math import fsum, gcd, lcm, log
from itertools import count
from collections import defaultdict
import sys

def factors(n):
    out = {}
    p = 2
    while p*p <= n:
        while n % p == 0:
            out[p] = out.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        out[n] = 1
    return out

def make(k):
    if k < 5:
        raise ValueError('k must be at least five')
    exps = {}
    budget = 1
    for threshold in count(2):
        fs = factors(threshold)
        if len(fs) == 1:
            p, e = next(iter(fs.items()))
            exps[p] = e
            budget += p - 1
            if budget >= k:
                break
    primes = sorted(exps)
    remainder = budget - k
    while remainder:
        p = primes[bisect_right(primes, remainder + 1) - 1]
        exps[p] -= 1
        assert exps[p] >= 0
        remainder -= p - 1
    primes = [p for p in primes if exps[p]]
    prior = 1
    data = []
    for p in primes:
        for j in range(1, exps[p]+1):
            terminal = (p == primes[-1] and j == exps[p])
            digits = range(p) if terminal else range(1, p)
            multipliers = {r**exps[r] for r in primes if r < p} if terminal else set()
            if len(multipliers) > len(digits) or prior < len(digits):
                return small_family(k)
            for d in range(1, prior+1):
                if len(multipliers) == len(digits):
                    break
                if prior % d == 0:
                    multipliers.add(d)
            if len(multipliers) != len(digits):
                return small_family(k)
            power = p**j
            for b, d in zip(digits, sorted(multipliers)):
                residue = d * ((b*(power//p) * pow(d, -1, power)) % power)
                data.append((power*d, residue))
        prior *= p**exps[p]
    return data

def small_family(k):
    # The terminal 3-row uses multipliers 1,2,2**(k-3); the other rows
    # successively cut the 2-adic digits. This also has defect zero.
    a = k-3
    data = [(2**j, 2**(j-1)) for j in range(1,a+1)]
    for b,d in enumerate([1,2,2**a]):
        data.append((3*d, d*((b*pow(d,-1,3)) % 3)))
    return data

def check(data,k):
    moduli = [n for n,_ in data]
    assert len(data) == len(set(moduli)) == k
    period = lcm(*moduli)
    # Factor modest moduli individually, never the potentially huge period.
    all_factors = [factors(n) for n in moduli]
    exps = {}
    for fs in all_factors:
        for p,e in fs.items():
            exps[p] = max(exps.get(p,0),e)
    assert k == 1 + sum((p-1)*e for p,e in exps.items())
    rows = defaultdict(list)
    for (n,a), fs in zip(data,all_factors):
        p = max(fs)
        power = p**fs[p]
        d = n//power
        assert a % d == 0 and a % (power//p) == 0
        rows[p,power].append((d,(a//(power//p)) % p))
    for (p,power), cells in rows.items():
        last = (p == max(exps) and power == p**exps[p])
        assert sorted(b for _,b in cells) == list(range(0 if last else 1,p))
        if last:
            assert lcm(*(d for d,_ in cells))*power == period
    if period <= 5000:
        assert all(any((x-a)%n == 0 for n,a in data) for x in range(period))
    return max(moduli), fsum(1/n for n in moduli)

if __name__ == '__main__':
    sizes = list(map(int,sys.argv[1:])) if len(sys.argv)>1 else [100,1000,10000,100000]
    for k in sizes:
        M, rho = check(make(k),k)
        print(f'{k:8d} {M:10d} {rho:12.8f} {rho/log(k):10.6f}')
