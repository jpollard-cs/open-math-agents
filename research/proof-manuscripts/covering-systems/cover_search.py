"""Exact reachability in the binary residue tree. Only prime-to-two part is enumerated."""
from functools import lru_cache
from itertools import combinations
from math import lcm


@lru_cache(maxsize=200000)
def can_cover(moduli):
    """Return whether some freely chosen residues cover every integer."""
    period = lcm(*moduli)
    if sum(period//m for m in moduli) < period:
        return False
    if not moduli:
        return False
    levels = (period & -period).bit_length() - 1
    odd = period >> levels
    full = (1 << odd) - 1
    jobs = []
    for m in moduli:
        i = (m & -m).bit_length() - 1
        t = m >> i
        masks = [sum(1 << x for x in range(r,odd,t)) for r in range(t)]
        jobs.append((i, t, masks))
    jobs.sort()
    remaining = [0]*(len(jobs)+1)
    for j in reversed(range(len(jobs))):
        i,t,_ = jobs[j]
        remaining[j] = remaining[j+1]+(period >> i)//t

    @lru_cache(maxsize=None)
    def visit(j, nodes, depth):
        if not nodes:
            return True
        if j == len(jobs):
            return False
        if (sum(mask.bit_count() for mask in nodes) << (levels-depth)) > remaining[j]:
            return False
        i,_,patterns = jobs[j]
        if depth < i:
            # Identical descendants are exchangeable. The jobs at all subsequent
            # levels can choose any one of them independently.
            return visit(j, tuple(x for x in nodes for _ in range(1 << (i-depth))), i)
        successors = set()
        for n,old in enumerate(nodes):
            if n and old == nodes[n-1]:
                continue
            for covered in patterns:
                new = old & ~covered
                if new == old:
                    continue
                children = list(nodes)
                if new: children[n] = new
                else: children.pop(n)
                successors.add(tuple(sorted(children)))
        return any(visit(j+1, s, depth) for s in sorted(successors,key=lambda s:sum(x.bit_count() for x in s)))
    return visit(0,(full,),0)


def irreducible(S):
    S=tuple(sorted(S))
    return can_cover(S) and all(not can_cover(S[:j]+S[j+1:]) for j in range(len(S)))


if __name__ == '__main__':
    for base,k,mx in [(72,8,36),(144,9,48),(144,10,48),(120,11,40),(240,12,80)]:
        ds=[m for m in range(2,mx) if base%m==0]
        count=0
        for choose in combinations(ds,k-1):
            S=choose+(mx,)
            if lcm(*S)!=base or not irreducible(S): continue
            print('witness',base,k,S,flush=True)
            count+=1
            break
        print('found',base,k,count,flush=True)
