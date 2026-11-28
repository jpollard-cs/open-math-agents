"""Check all subsets of a small labelled integer multigraph, recomputing its largest core by subsets."""
from itertools import product, combinations

left, right = (3,5), (7,11)
vertices = left+right
edges = sorted((p*q*d,p,q) for p,q,d in product(left,right,(1,2,4)))
assert len({n for n,p,q in edges}) == len(edges)


def endpoint_degrees(active, selected):
    return {v:sum(v in (p,q) and p in active and q in active for n,p,q in selected)
            for v in active}


def slot_check(family, cap):
    full = set(vertices)
    survivors = set(full)
    peeled = []
    while True:
        degree = endpoint_degrees(survivors,family)
        bad = [v for v in survivors if degree[v] < cap[v]]
        if not bad:
            break
        v = min(bad)
        removed = [n for n,p,q in family if v in (p,q) and p in survivors and q in survivors]
        assert len(removed)<cap[v]
        peeled.extend(removed)
        survivors.remove(v)
    # Direct enumeration of all feasible induced vertex sets checks maximality.
    for mask in range(16):
        subset = {v for i,v in enumerate(vertices) if mask>>i & 1}
        if all(d>=cap[v] for v,d in endpoint_degrees(subset,family).items()):
            assert subset <= survivors
    slots = {v:[] for v in survivors}
    rejected = []
    for n,p,q in family:
        if p not in survivors or q not in survivors:
            continue
        owner = next((v for v in (p,q) if len(slots[v])<cap[v]), None)
        if owner is None:
            rejected.append((n,p,q))
        else:
            slots[owner].append(n)
    records = peeled+[n for pool in slots.values() for n in pool]+[n for n,p,q in rejected]
    assert sorted(records) == [n for n,p,q in family]
    for n,p,q in rejected:
        for v in (p,q):
            assert len(slots[v]) == cap[v] and all(m<n and m%v==0 for m in slots[v])
            assert n//v >= cap[v]+1
    return len(rejected)


if __name__=='__main__':
    cases = rejected = 0
    for mask in range(1<<len(edges)):
        selected = [e for i,e in enumerate(edges) if mask>>i & 1]
        for quotas in ((1,1,1,1),(2,2,2,2),(1,2,3,2),(3,2,1,2)):
            rejected += slot_check(selected,dict(zip(vertices,quotas)))
            cases += 1
    print(cases, "labelled multigraph/quota instances;", rejected, "unassigned rows with complete earlier lists")
