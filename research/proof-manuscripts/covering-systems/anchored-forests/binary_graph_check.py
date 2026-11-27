"""Independent finite test of the binary one-hole classification."""
from functools import lru_cache
from itertools import combinations,permutations,product

def min_solutions(n, counts):
    """Minimize remaining assignments over all labels; report 2 for any minimum >=2."""
    spaces=[]
    for (a,b),t in zip(combinations(range(n),2),counts):
        if t==0:continue
        cells=[sum(1<<x for x in range(1<<n) if 2*((x>>a)&1)+((x>>b)&1)==v) for v in range(4)]
        spaces.append(tuple(sum(mask) for mask in combinations(cells,t)))
    spaces.sort(key=lambda xs:-max(x.bit_count() for x in xs))
    @lru_cache(None)
    def search(i,survive):
        if not survive:return 0
        if i==len(spaces):return min(2,survive.bit_count())
        best=2
        for rest in sorted({survive&~s for s in spaces[i]},key=int.bit_count):
            best=min(best,search(i+1,rest))
            if best==0:break
        return best
    return search(0,(1<<(1<<n))-1)

@lru_cache(None)
def reorders(n):
    pairs=list(combinations(range(n),2))
    return [tuple(pairs.index(tuple(sorted((pi[a],pi[b])))) for a,b in pairs) for pi in permutations(range(n))]

def connected(vertices,edges):
    if not vertices:return False
    reached={min(vertices)}
    while True:
        extra={b for a,b in edges if a in reached}|{a for a,b in edges if b in reached}
        if extra<=reached:return reached==vertices
        reached|=extra

def theta(n,counts):
    vertices=set(range(n))
    edges=[tuple(pair) for pair,t in zip(combinations(range(n),2),counts) for _ in range(t)]
    while True:
        deg={v:sum(v in e for e in edges) for v in vertices}
        leaves={v for v,k in deg.items() if k<2}
        if not leaves:break
        vertices-=leaves;edges=[e for e in edges if not leaves.intersection(e)]
    branch=[v for v in vertices if deg[v]==3]
    return (len(branch)==2 and all(t in (2,3) for t in deg.values())
            and tuple(sorted(branch)) in edges
            and all(connected(vertices,edges[:i]+edges[i+1:]) for i in range(len(edges))))

def run():
    simple=count=0;prev={()}
    for n in range(1,7):
        if n==1:types={()}
        else:
            types=set();pairs=list(combinations(range(n),2))
            for g in prev:
                old=dict(zip(combinations(range(n-1),2),g))
                for nbr in range(1,1<<(n-1)):
                    edge=tuple((nbr>>a)&1 if b==n-1 else old[a,b] for a,b in pairs)
                    # Byte strings give speedy lexicographic canonical comparison.
                    types.add(min(bytes(edge[i] for i in perm) for perm in reorders(n)))
        for g in types:
            assert (min_solutions(n,g)==1)==theta(n,g),g
        simple+=len(types);prev=types
    assert simple==143
    for n in (2,3,4):
        pairs=list(combinations(range(n),2))
        for counts in product(range(4),repeat=len(pairs)):
            if any(tuple(counts[i] for i in p)<counts for p in reorders(n)):continue
            if not connected(set(range(n)),[e for e,t in zip(pairs,counts) if t]):continue
            assert (min_solutions(n,counts)==1)==theta(n,counts),counts
            count+=1
    print(simple,'connected simple graph types through six vertices and',count,'connected loopless multigraph types through four vertices at multiplicity at most three; every prediction matched')

if __name__=='__main__':run()
