"""Integer and rational replay of adaptive projection bounds with free choices."""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from math import lcm


def run(moduli, start, thresholds, reverse):
    points = set(start)
    remaining = list(moduli)
    bound = Fraction(len(points))
    removed = []
    while True:
        chosen = None
        for n in (remaining[::-1] if reverse else remaining):
            freq = Counter(x % n for x in points)
            for a, count in sorted(freq.items(), reverse=reverse):
                if count*thresholds[n] >= len(points):
                    chosen = n,a
                    break
            if chosen:
                break
        if not chosen:
            break
        n,a=chosen
        removed.append((n,a))
        remaining.remove(n)
        points={x for x in points if x%n != a}
        bound *= 1 - 1/thresholds[n]
        assert points
    direct = {x for x in start if all(x%n != a for n,a in removed)}
    assert direct == points and len(points) <= bound
    for n in remaining:
        freq=Counter(x%n for x in points)
        assert max(freq.values())*thresholds[n] < len(points)
        for d in range(1,n+1):
            if n%d:
                continue
            marg=Counter(x%d for x in points)
            good={a for a,v in marg.items() if 2*d*v >= len(points)}
            assert 2*sum(marg[a] for a in good) >= len(points)
            for a,v in freq.items():
                if a%d in good:
                    assert v*thresholds[n] < 2*d*marg[a%d]
    for take in (1,2):
        for ns in combinations(remaining,take):
            cost=sum(1/thresholds[n] for n in ns)
            if cost>=1:
                continue
            for rs in product(*(range(n) for n in ns)):
                live=sum(all(x%n != a for n,a in zip(ns,rs)) for x in points)
                assert live >= len(points)*(1-cost)
    return len(removed),len(remaining)


def main():
    checks = eliminations = retained = 0
    # Only start if *every* complete placement misses a real point.
    for ns in ((2,3),(2,4),(3,4),(2,3,6),(3,4,6)):
        period=lcm(*ns)
        all_rows=list(product(*(range(n) for n in ns)))
        for phase in range(1, min(2**period,256)):
            start=[x for x in range(period) if phase >> x & 1]
            if not all(any(all(x%n!=r for n,r in zip(ns,rs)) for x in start)
                       for rs in all_rows):
                continue
            for denom, rev in product((2,3,4,5),(False,True)):
                hs={n:Fraction(n+denom,denom) for n in ns}
                used,left=run(ns,start,hs,rev)
                checks+=1
                eliminations+=used
                retained+=left
    print(checks,'free-placement projected domains and threshold/order choices;',
          eliminations,'greedy assignments;',retained,'jointly diffuse survivors.')
if __name__=='__main__':
    main()
