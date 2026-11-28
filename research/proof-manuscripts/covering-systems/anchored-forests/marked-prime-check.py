"""Finite cross-checks for simultaneous marked deletion and the moment argument."""
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm, prod
from random import Random


def moment_tests():
    tests = aligned = 0
    for ds in ((1,2,3),(2,3,4),(2,3,6),(3,4,5),(2,4,8)):
        period = lcm(*ds)
        envelopes = {r: sum(F(1, lcm(*seq)) for seq in product(ds,repeat=r))
                     for r in (2,3,4)}
        for a in product(*(range(d) for d in ds)):
            hits = [sum(x%d == b for d,b in zip(ds,a)) for x in range(period)]
            for r, upper in envelopes.items():
                actual = F(sum(h**r for h in hits), period)
                assert actual<=upper
                if not any(a):
                    assert actual==upper
                    aligned += 1
                tests += 1
    return tests,aligned


def owner_fibres():
    # Include prime powers and genuinely three-prime constraints. Check all
    # low fibres by enumerating the actual high tuple independently.
    rng = Random(423)
    qs = (3,5,7)
    low = 8
    period = low*prod(qs)
    templates = [d*prod(S) for d in (1,2,4,8) for t in (1,2,3)
                 for S in combinations(qs,t)]
    strict = thresholds = checked = covered = 0
    for run in range(260):
        family = rng.sample(templates, 2+run%23)
        a = {n:rng.randrange(n) for n in family}
        for z in range(low):
            active = []
            for n in family:
                support = tuple(q for q in qs if not n%q)
                h = prod(support)
                d = n//h
                if z%d == a[n]%d:
                    active.append((support,h,a[n]%h))
            frees = {q:set(range(q)) for q in qs}
            for support,h,r in active:
                if len(support)==1:
                    frees[h].discard(r)
            # Count extensions by a CRT tuple test, then by integer residues.
            explicit = sum(all(x%n!=a[n] for n in family) for x in range(z,period,low))
            by_tuples = sum(all(any(values[qs.index(q)] != r%q for q in supp)
                                for supp,h,r in active if len(supp)>1)
                            for values in product(*(frees[q] for q in qs)))
            assert explicit==by_tuples
            maxarity = max((len(s) for s,h,r in active),default=1)
            loads = [sum(F(1,h) for s,h,r in active if q in s) for q in qs]
            if max(loads) < F(1,8*maxarity):
                assert explicit>0
                strict += 1
            if not explicit:
                assert max(loads)>=F(1,8*maxarity)
                covered += 1
            # This sharper per-event condition can fire also in dense examples.
            if all(2*F(1,h)<1 and sum(2*F(1,k) for v,k,a in active
                                       if set(s)&set(v))<=F(1,2) for s,h,r in active):
                assert explicit
                thresholds += 1
            checked += 1
    # Strip one prime power digit too: a single p^2 event has weight p^-2.
    for a,b,c in product(range(9),range(5),range(3)):
        mods=(9,5,15)
        holes=[x for x in range(45) if all(x%n!=r%n for n,r in zip(mods,(a,b,c)))]
        tuples=[(i,j) for i,j in product(range(9),range(5)) if i!=a and j!=b
                and (i%3!=c%3 or j!=c%5)]
        assert len(holes)==len(tuples)>0
        checked += 1
    return checked,strict,thresholds,covered


def mark_deletions():
    family=(2,3,4,6,12)
    period=lcm(*family)
    tests=successes=0
    for residues in product(*(range(n) for n in family)):
        if not all(any(x%n==r for n,r in zip(family,residues)) for x in range(period)):
            continue
        successes += 1
        for marks in ((2,), (3,), (2,3), (3,5), (5,7)):
            old=[(n,r) for n,r in zip(family,residues) if all(n%p for p in marks)]
            holes={x for x in range(period) if all(x%n!=r for n,r in old)}
            old_period=lcm(*(n for n,r in old))
            seen={x%old_period for x in holes}
            assert len(holes)*old_period==len(seen)*period
            if marks in ((3,), (3,5)):
                assert all(sum(x%(n//3)==r%(n//3) for n,r in zip(family,residues)
                               if not n%3)>=3 for x in holes)
            tests+=1
    return successes,tests


def smooth_divisor_constructor():
    count=0
    for T in (75,100,143,225,480):
        for y in range(3,20):
            primes=[n for n in range(2,y+1) if all(n%d for d in range(2,n))]
            powers=[]
            for p in primes:
                v=p
                while v*p<=T:
                    v*=p
                powers.append(v)
            N=lcm(*powers)
            smooth=[]
            for n in range(1,T+1):
                d=n
                for p in primes:
                    while not d%p:
                        d//=p
                if d==1:
                    smooth.append(n)
            assert smooth==[n for n in range(1,T+1) if not N%n]
            assert all(v in smooth for v in powers)
            assert lcm(*smooth)==N
            count+=1
    return count


if __name__=='__main__':
    print('shifted moment tests, exact aligned cases:', *moment_tests())
    print('high fibres, small-load cases, local-neighborhood cases, covered fibres:', *owner_fibres())
    print('successful integer assignments and marked deletions:', *mark_deletions())
    print('bounded smooth-divisor periods:',smooth_divisor_constructor())
