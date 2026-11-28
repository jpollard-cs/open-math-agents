"""Finite exact rational checks for extracting common cofactors by two samples."""
from fractions import Fraction as F
from itertools import product
from random import Random


def check(sides, weights, triples):
    left, right, last = sides
    a, b, c = weights
    rho = sum((a[x]*b[y]*c[z] for x,y,z in triples), F(0))
    expected = distinct_contribution = F(0)
    for x,x2 in product(left, repeat=2):
        pairs = {(y,z) for y,z in product(right,last) if (x,y,z) in triples and (x2,y,z) in triples}
        density = sum((b[y]*c[z] for y,z in pairs), F(0))
        after = distinct = F(0)
        for y,y2 in product(right, repeat=2):
            mass = sum((c[z] for z in last if (y,z) in pairs and (y2,z) in pairs), F(0))
            after += b[y]*b[y2]*mass
            if y != y2:
                distinct += b[y]*b[y2]*mass
        assert after >= density**2
        assert distinct >= after - sum(v*v for v in b)
        expected += a[x]*a[x2]*density
        if x != x2:
            distinct_contribution += a[x]*a[x2]*density
    assert expected >= rho**2
    assert distinct_contribution >= expected - sum(v*v for v in a)


def run():
    rng = Random(1189)
    cases = 0
    for shape in [(2,2,2),(3,4,5)]:
        sides = tuple(range(n) for n in shape)
        entries = list(product(*sides))
        weights = []
        for n in shape:
            raw = [F(1, 3+2*i) for i in range(n)]
            weights.append([r/sum(raw) for r in raw])
        families = (range(1<<len(entries)) if len(entries)==8
                    else (rng.getrandbits(len(entries)) for _ in range(144)))
        for mask in families:
            check(sides,weights,{e for j,e in enumerate(entries) if mask>>j & 1})
            cases += 1
    print(cases, "weighted three-partite relations checked")


if __name__ == "__main__":
    run()
