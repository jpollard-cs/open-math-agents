"""Construct an irreducible integer cover with a prescribed normalized largest modulus."""
from collections import Counter
from fractions import Fraction
from math import lcm

from seed_certificates import SEEDS

SEED_RESIDUES = {3: (0,0,1,1,11,5,7,5,31,13),
                 5: (0,0,0,1,1,7,2,3,13,29,13)}


def prime_factors(n):
    factors = []
    p = 2
    while p*p <= n:
        while n % p == 0:
            factors.append(p)
            n //= p
        p = 3 if p == 2 else p + 2
    if n > 1: factors.append(n)
    return factors


def split(cover, m, p, divisors):
    """Replace one congruence by p congruences; divisors are before p-multiplication."""
    L = lcm(*cover)
    if L//m % p == 0 or len(set(divisors)) != p or m not in divisors:
        raise ValueError("invalid split")
    if any(m%h or m//h%p == 0 for h in divisors):
        raise ValueError("a divisor lost part of the required prime power")
    residue = cover.pop(m)
    for j,h in enumerate(divisors):
        assert p*h not in cover
        cover[p*h] = (residue+j*m)%(p*h)


def double(cover):
    """Add one modulus, doubling the greatest modulus and preserving the ratio."""
    return {2: 1, **{2*m: 2*r for m,r in cover.items()}}


def frame(a,factors,anchor=False,side=False):
    u=1
    cover={2**i:2**(i-1) for i in range(1,a+1)}
    for stage,p in enumerate(factors):
        old=(1<<a)*u
        u*=p
        reserved=[]
        if anchor and stage == 0:
            assert len(factors)>1
            reserved.append(a)
        if side and stage == len(factors)-1:
            reserved.append(2)
        indices=reserved+[i for i in range(a) if i not in reserved]
        assert len(indices)>=p-1
        for digit,i in enumerate(indices[:p-1],1):
            modulus=(1<<i)*u
            assert modulus not in cover
            cover[modulus]=(digit*old)%modulus
    maximum=(1<<a)*u
    assert maximum not in cover
    cover[maximum]=0
    return cover


def grow_side(cover,side,steps):
    for _ in range(steps):
        # The side in these constructions is four times its odd part.
        assert side%4==0 and (side//4)%2
        split(cover,side,3,[side//4,side//2,side])
        side *= 3


def construct(u,d):
    """Return a dictionary modulus -> residue, or None if the ratio is impossible.

    Input: positive odd u and nonnegative d. The desired ratio is u / 2^(f(u)+d),
    where f(u) sums p-1 for all prime factors with multiplicity.
    """
    if u<1 or not u%2 or d<0:
        raise ValueError("u must be positive odd and d nonnegative")
    factors=prime_factors(u)
    prime=len(factors)==1
    if u==1 or (prime and d==1):
        return None
    if d%2 and u in SEEDS:
        n=(d-3)//2
        cover=dict(zip(SEEDS[u],SEED_RESIDUES[u]))
        side=36 if u==3 else 12
        while max(cover)<side*3**n:
            m=max(cover)
            split(cover,m,2,[m//u,m])
        grow_side(cover,side,n)
        return cover
    if d%2 and prime:
        # The three new classes in the first split have two small auxiliaries.
        n=(d-3)//2
        a=max(5,u-1,(12*3**n).bit_length())
        cover=frame(a,factors)
        binary=1<<a
        split(cover,binary,3,[4,8,binary])
        split(cover,3*binary,2,[binary,3*binary])
        grow_side(cover,12,n)
        return cover
    n=d//2
    a=max(p-1 for p in factors)
    if n:
        a=max(a,3,(4*3**n-1).bit_length())
    cover=frame(a,factors,anchor=bool(d%2),side=bool(n))
    if d%2:
        p=factors[0]
        binary=1<<a
        split(cover,p*binary,2,[binary,p*binary])
    grow_side(cover,4*u,n)
    return cover


def normalized(cover):
    return Fraction(max(cover),1 << (len(cover)-1))


def zero_defect_cover(maximum):
    """Return a minimum-size cover with this largest modulus, or None."""
    if maximum < 2:
        return None
    powers = sorted(Counter(prime_factors(maximum)).items())
    earlier_divisors = [1]
    cover = {}
    for index, (prime, exponent) in enumerate(powers):
        last_prime = index == len(powers) - 1
        required = prime if last_prime else prime - 1
        if len(earlier_divisors) < required:
            return None
        for level in range(1, exponent + 1):
            prime_power = prime ** level
            # The largest earlier divisor is last, so the final modulus is reserved.
            for digit, divisor in enumerate(earlier_divisors[:prime - 1], start=1):
                modulus = prime_power * divisor
                target = digit * (prime_power // prime)
                cover[modulus] = divisor * (target * pow(divisor, -1, prime_power) % prime_power)
        if not last_prime:
            earlier_divisors = sorted(
                divisor * prime ** level
                for divisor in earlier_divisors
                for level in range(exponent + 1)
            )
    assert maximum not in cover
    cover[maximum] = 0
    return cover


def fixed_size(k,m):
    """A decision and, when available, explicit residues. Exact above the proven cutoff."""
    if k<1 or m<2:
        return 'impossible',None
    binary=m&-m
    a=binary.bit_length()-1
    u=m//binary
    factors=prime_factors(u)
    d=k-1-a-sum(p-1 for p in factors)
    prime_power = bool(factors) and factors[0]==factors[-1]
    if (d<0 or u==1 or (len(factors)==1 and d==1) or
        (prime_power and (a==0 or (d==0 and a<factors[0]-1)))):
        return 'impossible',None
    if d == 0:
        cover = zero_defect_cover(m)
        return ('attainable', cover) if cover is not None else ('impossible', None)
    cover=construct(u,d)
    if len(cover)>k:
        assert 9*m*m<=4*3**k
        return 'below cutoff; no witness from this construction',None
    while len(cover)<k:
        cover=double(cover)
    assert max(cover)==m
    return 'attainable',cover


if __name__=="__main__":
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--fixed',action='store_true',help='interpret arguments as set size k and largest modulus m')
    parser.add_argument('first',type=int)
    parser.add_argument('second',type=int)
    args=parser.parse_args()
    if args.fixed:
        status,cover=fixed_size(args.first,args.second)
    else:
        cover=construct(args.first,args.second)
        status='impossible' if cover is None else 'attainable'
    if cover is None:
        print(status)
    else:
        print("k =",len(cover),"largest modulus =",max(cover),"normalized =",normalized(cover))
        for m,r in sorted(cover.items()):
            print(f"{r} mod {m}")
