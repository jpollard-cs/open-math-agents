"""All binary diamond placements, all survivor-centered restrictions, and a direct two-block check."""
from itertools import product

edges = [(0,2), (2,1), (1,3), (3,0), (0,1)]
cube = list(product(range(2), repeat=4))


def hits(x, labels):
    return [i for i, ((a,b), pair) in enumerate(zip(edges, labels)) if (x[a], x[b]) == pair]


def run():
    count = triples = 0
    for labels in product(list(product(range(2), repeat=2)), repeat=5):
        holes = [x for x in cube if not hits(x, labels)]
        assert holes
        if len(holes) != 1:
            continue
        z = holes[0]
        witnesses = []
        for i in range(4):
            x = tuple(u ^ (j == i) for j, u in enumerate(z))
            witnesses.append(hits(x, labels))
        opposite, = hits(tuple(1-u for u in z), labels)
        assert len(set([opposite] + [j for choices in witnesses for j in choices])) == 5
        assert all(len(v) == 1 for v in witnesses)
        count += 1
        # For two independent copies, test every binary reference in the
        # smallest rectangle containing their two axes (here the whole cube).
        for ref in product(range(2), repeat=8):
            if sum(u != v for u, v in zip(ref, z+z)) > 1:
                continue
            a,b = edges[opposite]
            assert not all(any(ref[offset+i] != z[i] for i in (a,b)) for offset in (0,4))
            triples += 1
    return count, triples


if __name__ == "__main__":
    print("unique-hole placements and paired terminal-compatible references:", run())
