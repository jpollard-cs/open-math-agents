"""Brute-force all residue and digit assignments, independent of the pair formula."""
from itertools import combinations, combinations_with_replacement
from math import gcd, lcm, isqrt


def actual(e, p):
    base = lcm(*e)
    masks = []
    for d in e:
        masks.append(tuple(sum(1 << (p*x+b) for x in range(a, base, d))
                           for a in range(d) for b in range(p)))
    states = {0}
    for row in masks:
        states = {u | v for u in states for v in row}
    filled = set()
    all_digits = (1 << p) - 1
    for state in states:
        filled.add(tuple(x for x in range(base)
                         if ((state >> (p*x)) & all_digits) == all_digits))
    return base, filled


def valuation_rule(e, p):
    if len(e) >= 2*p:
        return 1
    threshold = 2*(len(e)-p)+1
    bound = lcm(*e)
    ans = 1
    for q in range(2, bound+1):
        if any(q % n == 0 for n in range(2, int(q**0.5)+1)):
            continue
        power = q
        while sum(d % power == 0 for d in e) >= threshold:
            ans *= q
            power *= q
    return ans


def run():
    count = pairs = 0
    for p, choices, maxt in [(2, (1, 3), 5), (3, (1, 2, 4), 6), (5, (1, 2), 7)]:
        for t in range(1, maxt+1):
            for e in combinations_with_replacement(choices, t):
                B, filled = actual(e, p)
                differences = {(x-y) % B for S in filled for x in S for y in S}
                predicted = {u for u in range(B) if t>=p and sum(u % d == 0 for d in e)>=2*p-t}
                assert differences == predicted
                if t >= p:
                    assert gcd(B, *differences) == valuation_rule(e,p)
                pairs += B*B
                count += 1
    B, filled = actual((1,3,9),2)
    assert all(any(a in S and b in S for S in filled) for a,b in [(0,1),(0,2),(1,2)])
    assert not any({0,1,2}.issubset(S) for S in filled)
    print('Exhaustive packets:', count, 'ordered site pairs:', pairs)
    print('All realized differences and forced moduli agreed.')
    print('Top moduli 2,6,18 cover every pair from 0,1,2 modulo 9, and never all three together.')


def joint(two_p, two_q, counts):
    a,b,c,d,g,h = counts
    t = g+h
    for i in range(b+1):
        for j in range(d+1):
            u = max(0,two_p-a-i)
            uu = max(0,two_p-a-b+i)
            v = max(0,two_q-c-j)
            vv = max(0,two_q-c-d+j)
            if u*v + uu*vv - min(g,min(u,uu)*min(v,vv)) <= t:
                return True
    return False


def joint_brute():
    # Literal sets of hit cells. No rectangle or capacity formula is used.
    p,q = 2,3
    full=(1<<(2*p*q))-1
    size=p*q
    def masks_for(kind,shared):
        shapes=[]
        for a in range(p if kind != 'q' else 1):
            for b in range(q if kind != 'p' else 1):
                mask=sum(1<<(i*q+j) for i in range(p) for j in range(q)
                         if (kind=='q' or i==a) and (kind=='p' or j==b))
                shapes.extend([mask | mask<<size] if shared else [mask,mask<<size])
        return shapes
    types=[masks_for(kind,share) for kind in ('p','q','pq') for share in (True,False)]
    tests=0
    def verify(prefix,states,room):
        nonlocal tests
        if len(prefix)==len(types):
            assert (full in states)==joint(p,q,prefix),prefix
            tests+=1
            return
        ms=types[len(prefix)]
        current=states
        for count in range(room+1):
            verify(prefix+[count],current,room-count)
            if count<room:
                current={m|s for m in ms for s in current}
    verify([], {0}, 7)
    print('Joint two-prime criterion vs full 12-cell enumeration:',tests,'count vectors.')


def check_runs():
    checks=0
    for p,allowed in [(2,(1,3,5)),(3,(1,2,4)),(5,(1,2))]:
        for t in range(1,len(allowed)+1):
            for es in combinations(allowed,t):
                base,filled=actual(es,p)
                for width in range(1,min(base,p+1)+1):
                    available=sum(1+(width-1)//d for d in es)
                    brute=any(all(x in s for x in range(width)) for s in filled)
                    assert (available>=p*width)==brute
                    checks+=1
    inverse=0
    for p in range(2,130):
        if any(p%q==0 for q in range(2,isqrt(p)+1)):
            continue
        for width in range(1,p+1):
            cost=p*width-sum((width-1)//d for d in range(1,width))
            T=cost+(cost-1)//(p-1)
            assert T-T//p==cost and T-1-(T-1)//p==cost-1
            assert cost+sum((width-1)//d for d in range(1,min(T,width-1)+1) if d%p)==p*width
            inverse+=1
    print('Interval criterion:',checks,'direct choices; exact inverse:',inverse,'prime/length pairs.')


if __name__ == '__main__':
    run()
    joint_brute()
    check_runs()
