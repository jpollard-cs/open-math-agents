"""AI-authored exact-cardinality constructor for Erdős 1189(ii), Python 3.9+."""
from bisect import bisect_right
from math import gcd, isqrt, lcm
from itertools import count
import argparse


def primes_through(limit):
    sieve = bytearray([1]) * (limit + 1)
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p*p::p] = bytes((limit - p*p) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def digit_levels(k):
    limit = 16
    while True:
        primes = primes_through(limit)
        # Events in the full lcm(1,...,q), in increasing prime-power order.
        events = []
        for p in primes:
            power = p
            while power <= limit:
                events.append((power, p))
                power *= p
        events.sort()
        maximum_size = 1
        exponents = {}
        for power, p in events:
            maximum_size += p - 1
            exponents[p] = exponents.get(p, 0) + 1
            if power == p and maximum_size >= k:
                q = p
                deficit = maximum_size - k
                # Largest available distinct coin p-1. Never remove terminal q.
                end = bisect_right(primes, q - 1)
                while deficit:
                    i = bisect_right(primes, deficit + 1, 0, end) - 1
                    if i < 0:
                        return None
                    r = primes[i]
                    exponents[r] -= 1
                    deficit -= r - 1
                    end = i
                return [(r,e) for r,e in sorted(exponents.items()) if e]
        limit *= 2


def assign(levels, large_cofactors=False, bulk_rule=None):
    q = levels[-1][0]
    prefix = 1
    prefix_tau = 1
    maximal_powers = []
    classes = {}
    for pos, (p,e) in enumerate(levels):
        for j in range(1, e + 1):
            final = pos == len(levels) - 1 and j == e
            required = p if final else p - 1
            if required > prefix_tau:
                return None
            ds = set(maximal_powers if final else ())
            if len(ds) > required:
                return None
            for d in count(1):
                if len(ds) == required:
                    break
                if prefix % d == 0:
                    ds.add(d)
            if large_cofactors and not final and p*p > q:
                # Choose the largest permissible divisors under the same cap.
                ceiling = max(max(ds), q*q // p)
                ds = set()
                for d in range(ceiling, 0, -1):
                    if prefix % d == 0:
                        ds.add(d)
                        if len(ds) == required:
                            break
                assert len(ds) == required
            if bulk_rule is not None and not final and p*p > q:
                ds = bulk_rule(prefix, p, q, ds)
            power = p**j
            for digit, d in enumerate(sorted(ds), 0 if final else 1):
                modulus = d * power
                assert modulus not in classes
                # Solve x = 0 mod d and x = digit*p^(j-1) mod power.
                classes[modulus] = d * ((digit * (power//p) * pow(d,-1,power)) % power)
        prefix *= p**e
        prefix_tau *= e + 1
        maximal_powers.append(p**e)
    return classes


def construct(k, large_cofactors=False, bulk_rule=None):
    if k < 5:
        raise ValueError("the construction requires k >= 5")
    levels = digit_levels(k)
    classes = assign(levels, large_cofactors, bulk_rule) if levels is not None else None
    if classes is None:
        levels = [(2,k-3), (3,1)]
        # The fallback uses maximal power 2^(k-3), 1 and 2 as final multipliers.
        classes = assign(levels)
    assert classes is not None and len(classes) == k
    return classes, levels


def verify(classes, levels, brute_limit=200000):
    # Reconstruct each digit and cofactor from the actual congruences.
    # Reassignment is ruled out by the final LCM and the per-level counts.
    unassigned = dict(classes)
    prefix = 1
    for pos,(p,e) in enumerate(levels):
        for j in range(1,e+1):
            power = p**j
            ds, digits, processed = [], [], []
            for n,r in unassigned.items():
                if n % power or prefix % (n//power):
                    continue
                d = n//power
                assert gcd(d,p)==1 and r % d == 0 and r % (power//p)==0
                ds.append(d)
                digits.append((r//(power//p)) % p)
                processed.append(n)
            for n in processed:
                del unassigned[n]
            final = (pos == len(levels)-1 and j == e)
            assert sorted(digits)==list(range(0 if final else 1,p))
            if final:
                assert lcm(*ds)==prefix
        prefix *= p**e
    assert not unassigned
    assert len(classes)==1+sum((p-1)*e for p,e in levels)
    if prefix > brute_limit:
        return False
    counts = bytearray(prefix)
    for n,r in classes.items():
        for x in range(r,prefix,n):
            counts[x] += 1
    assert min(counts) and all(any(counts[x]==1 for x in range(r,prefix,n))
                               for n,r in classes.items())
    divisors = [(1,0)]
    for p,e in levels:
        divisors = [(d*p**j,c+j*(p-1)) for d,c in divisors for j in range(e+1)]
    for d,c in divisors:
        if d != prefix:
            assert sum(d % n==0 for n in classes)<=c
    return True


def tests():
    brute = 0
    for k in range(5,1001):
        classes,levels = construct(k)
        brute += verify(classes,levels)
    print("exact sizes 5..1000; full-period and all-divisor checks:", brute)
    for k in range(5,1001):
        classes,levels = construct(k, True)
        verify(classes,levels)
    for k in (100,1000,10000,100000):
        classes,levels = construct(k)
        assert len(classes)==k
        verify(classes,levels)
        large,large_levels = construct(k,True)
        verify(large,large_levels)
        print("k, terminal prime, maximum in each construction, normalized means:",
              k, levels[-1][0], max(classes), max(large),
              round(sum(classes)/(k*max(classes)),6), round(sum(large)/(k*max(large)),6))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("k",nargs="?",type=int)
    parser.add_argument("--large-cofactors", action="store_true")
    args = parser.parse_args()
    if args.k is None:
        tests()
    else:
        classes,_ = construct(args.k, args.large_cofactors)
        for n,r in sorted(classes.items()):
            print(n,r)
