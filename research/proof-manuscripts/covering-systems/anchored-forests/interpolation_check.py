"""Compare the cycle criterion to free row reassignments on small binary grids."""
from functools import lru_cache
from itertools import combinations,product

def cycle(owners, supports):
    # Keep arcs only to different owners, so a directed two-cycle is impossible.
    arcs={g:{owners[i] for i in supports[g] if owners[i]!=g} for g in supports}
    def visit(g,path):
        if g in path:return True
        return any(visit(h,path|{g}) for h in arcs[g])
    return any(visit(g,set()) for g in arcs)

def min_holes(n,sizes):
    pts=list(product(range(2),repeat=n)); all_mask=(1<<len(pts))-1
    best=[0]
    for support,number in sizes:
        cells={}
        for j,x in enumerate(pts):
            proj=tuple(x[i] for i in support)
            cells[proj]=cells.get(proj,0)|(1<<j)
        # WLOG repeat no cell when maximizing coverage.
        masks={sum(group) for group in combinations(cells.values(),number)}
        best={a|b for a in best for b in masks}
        # A strict subset can be replaced by a larger reachable union.
        maximal=[]
        for a in sorted(best,key=int.bit_count,reverse=True):
            if not any((a&m)==a for m in maximal):maximal.append(a)
        best=maximal
    return len(pts)-max(m.bit_count() for m in best)

def check(n,family):
    options=[[i for i,g in enumerate(family) if v in g] for v in range(n)]
    profiles=singleton=0
    @lru_cache(maxsize=None)
    def lower(sizes):return min_holes(n,sizes)
    for owners in product(*options):
        active={g:family[g] for g in set(owners)}
        sizes=tuple((s,2**owners.count(g)-1) for g,s in sorted(active.items()))
        smallest=lower(sizes);predicted=not cycle(owners,active)
        assert smallest>=1 and (smallest==1)==predicted
        for j,(s,t) in enumerate(sizes):
            assert lower(sizes[:j]+((s,t-1),)+sizes[j+1:])>=2
        profiles+=1; singleton+=predicted
    print(n,'variables',profiles,'allocations',singleton,'attain a single hole; checked all deletion types')

if __name__=='__main__':
    check(3,[s for t in (1,2,3) for s in combinations(range(3),t)])
    check(4,[(i,) for i in range(4)]+[(0,1),(1,2),(2,3),(0,3),(0,1,2),(1,2,3)])
