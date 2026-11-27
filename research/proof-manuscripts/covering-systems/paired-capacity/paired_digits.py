"""Construct and independently check finite instances of the paired-digit theorem.

Run python paired_digits.py or python paired_digits.py 101 --export cover.json.
Only Python's standard library is needed.
"""
import argparse
import json
from math import gcd, isqrt, lcm


def primes(n):
    sieve = bytearray(b'\x01') * (n + 1)
    sieve[:2] = b'\x00\x00'
    for p in range(2, isqrt(n) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes(1 + (n-p*p)//p)
    return [i for i, present in enumerate(sieve) if present]


def powers(p, limit):
    power = p
    while power <= limit:
        yield power
        power *= p


def cofactor_choices(old, required, last):
    result = []
    for d in range(1, last + 1):
        if old % d == 0:
            result.append(d)
            if len(result) == required:
                break
    return result


def plan(z):
    ps = primes(z)
    assert z >= 7 and ps[-1] == z
    cap = z*(z+1)
    old = 1
    offers = {}
    for i, p in enumerate(ps[:-1]):
        q = ps[i+1]
        if p >= 5 and q < z and p*q <= z:
            dress = cofactor_choices(old, p*q-1, cap//(p*q))
            if len(dress) == p*q-1:
                offers[p] = (q, dress)
        old *= max(powers(p,z+1))
    # Weighted path matching chooses an admissible subset of the adjacent pairs.
    score = [0]*(len(ps)+2)
    for i in reversed(range(len(ps))):
        p = ps[i]
        score[i] = score[i+1]
        if p in offers:
            q, _ = offers[p]
            score[i] = max(score[i], (p-1)*(q-1) + score[i+2])
    choices = {}
    i = 0
    while i < len(ps):
        p = ps[i]
        if p in offers and score[i] > score[i+1]:
            choices[p] = offers[p]
            i += 2
        else:
            i += 1
    return ps, choices


def construct(z, paired=True, binary=True):
    ps, choices = plan(z)
    if not paired:
        choices = {}
    stages = []
    def add(r, n):
        stages.append((r, list(n)))
    add(2, [2])  # retain one row and carry the distinguished index
    add(2, [4])
    for t in powers(3,z+1):
        add(3, [t,2*t])
    two = list(powers(2,z+1))[2:]
    i = 0
    while i < len(two):
        if binary and i+1 < len(two):
            t = two[i+1]
            add(4,[t,3*t,9*t])
            i += 2
        else:
            add(2,[two[i]])
            i += 1
    i = 2
    while i < len(ps)-1:
        p = ps[i]
        if p in choices:
            q, ds = choices[p]
            add(p*q,[p*q*d for d in ds])
            segment = (p,q)
        else:
            add(p,[p*d for d in range(1,p)])
            segment = (p,)
        for prime in segment:
            for t in list(powers(prime,z+1))[1:]:
                add(prime,[t*d for d in range(1,prime)])
        i += len(segment)
    add(z,[z*d for d in [*range(1,z),z+1]])
    return stages, list(choices.items())


def verify(stages, cap, enumerate_small=False):
    old = 1
    rows = {}
    for i,(r, fixed) in enumerate(stages):
        final = i == len(stages)-1
        packet = list(fixed) if final else [*fixed,r*old]
        assert len(packet) == r
        projections = [gcd(old,n) for n in packet]
        assert all(n == r*g for n,g in zip(packet,projections))
        assert lcm(*projections) == old
        for j,n in enumerate(fixed):
            assert n <= cap and n > 1 and n not in rows
            # j=1,...,r-1 are the fixed lifts in a nonterminal stage.
            rows[n] = (old*(j if final else j+1)) % n
        old *= r
    assert max(rows) == cap and lcm(*rows) == old
    if enumerate_small:
        assert all(any(t%n == a for n,a in rows.items()) for t in range(old))
    return rows


def zero_budget(cap):
    return 1+sum(p-1 for p in primes(isqrt(cap))
                 for _ in powers(p, cap//(p+1)))


def run(z, export=None):
    stages, pairs = construct(z)
    cap = z*(z+1)
    rows = verify(stages, cap, enumerate_small=z<=11)
    plain_stages,_ = construct(z, paired=False, binary=False)
    plain = verify(plain_stages,cap,enumerate_small=z<=11)
    pred = 1+sum(p-1 for p in primes(z) for _ in powers(p,z+1))
    assert pred == len(plain)
    binary_gain = (len(list(powers(2,z+1)))-2)//2
    assert len(rows) == pred+binary_gain+sum((p-1)*(q-1) for p,(q,_) in pairs)
    bound = zero_budget(cap)
    print(f'z={z}, cap={cap}, baseline={len(plain)}, constructed={len(rows)}, '
          f'zero-defect upper={bound}, pairs={[(p,q) for p,(q,_) in pairs]}')
    if export:
        with open(export, 'w') as out:
            json.dump({'terminal_prime':z,'stages':stages,'residues':rows},out)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('z', type=int, nargs='*', default=[7,11,43,97,149,223,307,503])
    parser.add_argument('--export')
    args = parser.parse_args()
    assert not args.export or len(args.z) == 1
    for z in args.z:
        run(z,args.export)
