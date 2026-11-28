"""Checks of cut-vertex quotas on full assignments and sharp finite stars."""
from collections import Counter
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
from pathlib import Path

spec = spec_from_file_location("component_check", Path(__file__).with_name("component-check.py"))
checks = module_from_spec(spec)
spec.loader.exec_module(checks)


def branch_sizes(vertices, shapes, root):
    active = set(vertices) - {root}
    branches = []
    while active:
        reached = {active.pop()}
        while True:
            new = set().union(*(s for s in shapes if s & reached)) & active
            if not new:
                break
            reached.update(new)
            active -= new
        branches.append(len(reached))
    return sorted(branches)


def cut_bounds(sizes, rows):
    counts = Counter()
    for part in checks.components(len(sizes),rows):
        vertices = [i for i in range(len(sizes)) if part >> i & 1]
        if len(vertices)==1:
            continue
        shapes = [{i for i in vertices if shape >> i & 1}
                  for shape,changed,_ in rows if changed & part]
        for i in vertices:
            branches = branch_sizes(vertices,shapes,i)
            unaries = shapes.count({i})
            assert len(branches)+unaries <= sizes[i]-1
            counts["checked"] += 1
            counts["cut_vertices"] += int(len(branches)>1)
    return counts


def explicit_stars():
    # All p-1 center labels except zero are assigned to different two-label leaves.
    stats = Counter()
    for p in range(3,15):
        sizes = (p,)+(2,)*(p-1)
        rows = []
        for j in range(1,p):
            shape = 1 | (1<<j)
            rows.extend([(shape,1,0), (shape,shape,0), (shape,1<<j,0)])
        observed = cut_bounds(sizes,rows)
        assert observed["cut_vertices"]==1
        stats["star_positions"] += observed["checked"]
        # Exhaust effective labels in a single branch, including repeated choices.
        # Two rows after an edge-row deletion, three before.
        for budget in (2,3):
            for size in range(1,budget+1):
                for cells in combinations(range(2*p),size):
                    feasible = [sum(2*i+c not in cells for c in (0,1)) for i in range(p)]
                    assert feasible.count(0)<=1
                    if budget==2 and feasible.count(0)==1:
                        assert 1 not in feasible
                    stats["branch_placements"] += 1
    return stats


if __name__ == "__main__":
    from math import prod
    stats = Counter()
    for sizes,bound in [((2,2),4),((2,3),5),((2,2,2),6)]:
        available = []
        for shape in range(1,2**len(sizes)):
            indices = [i for i in range(len(sizes)) if shape>>i & 1]
            for labels,mask in checks.all_classes(sizes,shape).items():
                changed = sum(1<<i for i,a in zip(indices,labels) if a)
                if changed:
                    available.append((shape,changed,mask))
        for k in range(1,bound+1):
            for rows in combinations(available,k):
                mask = 0
                for _,_,cover in rows:
                    mask |= cover
                if mask != (1<<prod(sizes))-2:
                    continue
                shapes = tuple(sorted(shape for shape,_,_ in rows))
                if checks.indispensable(sizes,shapes):
                    stats += cut_bounds(sizes,rows)
    print("small singleton placements",dict(stats))
    print("stars and all branch reassignments",dict(explicit_stars()))
