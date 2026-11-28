"""Compute the smallest number of moduli left over by any digit partition."""
from collections import Counter
from math import lcm, prod
from enumerate_covers import prime_powers

def partitions(items):
    if not items:
        yield ()
        return
    first, *rest = items
    for tail in partitions(rest):
        yield ((first,), *tail)
        for i, block in enumerate(tail):
            yield (*tail[:i], (first,*block), *tail[i+1:])

def unmatched(moduli, period=None):
    digits=[]
    for p, power in prime_powers(lcm(*moduli) if period is None else period):
        level=p
        while level <= power:
            digits.append((p,level))
            level *= p
    hist=Counter()
    for partition in partitions(digits):
        # A source modulus may occupy one adjacent slot; augmenting paths
        # on this bipartite graph give the largest number simultaneously placed.
        slots=[]
        for block in partition:
            divisor=lcm(*(q for _,q in block))
            capacity=prod(p for p,_ in block)-1
            possible=[i for i,m in enumerate(moduli) if m%divisor==0]
            slots.extend([possible]*min(capacity,len(possible)))
        matched={}
        def assign(slot,seen):
            for i in slots[slot]:
                if i in seen:
                    continue
                seen.add(i)
                previous=matched.get(i)
                if previous is None or assign(previous,seen):
                    matched[i]=slot
                    return True
            return False
        for slot in range(len(slots)):
            assign(slot,set())
        hist[len(moduli)-len(matched)]+=1
    return hist

if __name__=='__main__':
    import sys
    moduli=tuple(map(int,sys.argv[1:]))
    if len(moduli) < 2 or tuple(sorted(set(moduli))) != moduli:
        sys.exit('Supply distinct moduli in increasing order, including the largest.')
    hist=unmatched(moduli[:-1], lcm(*moduli))
    print('minimum unmatched:',min(hist))
    print('partitions by number unmatched:',dict(sorted(hist.items())))
