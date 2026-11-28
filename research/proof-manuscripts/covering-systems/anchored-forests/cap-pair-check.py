"""Direct finite checks of the two counting arguments in cap-pair-alternative.md."""
from fractions import Fraction as F
from itertools import combinations, product
from random import Random


def check_rectangles():
    rng = Random(1189)
    n, m, D = 6, 7, 24
    universe = set(product(range(n), range(m)))
    cases = retained = comparisons = 0
    for prob in (0.24, 0.38, 0.69, 0.83):
        for test in range(32):
            families = {edge: [d for d in range(1,D+1) if rng.random()<prob] for edge in universe}
            rho = F(sum(map(len,families.values())), n*m*D)
            pools = {e:ds[:int(rho*D/8)] for e,ds in families.items() if 4*len(ds) >= rho*D}
            layers = {d:{e for e in pools if d in families[e][len(pools[e]):]} for d in range(1,D+1)}
            assert sum(map(len,layers.values())) >= rho*n*m*D/2
            good = {d:es for d,es in layers.items() if len(es)>=rho*n*m/4}
            assert len(good)>=rho*D/4
            for d,es in good.items():
                assert all(all(t<d for t in pools[e]) for e in es)
            # Compute the expected two-layer intersection exactly in both orders.
            total = sum(len(a&b) for a,b in product(good.values(),repeat=2))
            counts = [sum(e in es for es in good.values()) for e in universe]
            assert total == sum(f*f for f in counts)
            assert total*n*m >= sum(counts)**2
            # A single erased-pair set acts on *all* layers and intersections.
            bad = set(rng.sample(sorted(universe),3))
            for a,b in combinations(good.values(),2):
                assert len((a-bad)&(b-bad)) >= len(a&b)-len(bad)
                comparisons += 1
            retained += len(good)
            cases += 1
    return cases,retained,comparisons


def simultaneous_collisions():
    # Exact expectation on non-product low relations and guards x mod p*d.
    rng = Random(20705)
    edges = {(p,q):tuple(range(1,8)) for p,q in product((3,5,7),(11,13))}
    checks = samples = 0
    for _ in range(45):
        H = rng.sample(range(210),6)
        w = [rng.randint(1,3) for x in H]
        W = sum(w)
        rows = [p*d for (p,q),ds in edges.items() for d in ds]
        pair_mass = 0
        for m in rows:
            mult = [sum(w[i] for i,x in enumerate(H) if x%m==r) for r in range(m)]
            assert sum(v*v for v in mult)<=W*max(mult)
            pair_mass += max(mult)
        # Weight each ordered triple with its actual product probability.
        total = 0
        best = len(rows)
        for i,j,k in product(range(len(H)),repeat=3):
            collisions = sum(len({H[i]%m,H[j]%m,H[k]%m})<3 for m in rows)
            total += w[i]*w[j]*w[k]*collisions
            best = min(best,collisions)
            samples += 1
        assert best*W**3 <= total <= 3*pair_mass*W**2
        checks += 1
    return checks,samples


if __name__=='__main__':
    print('rectangles, retained layers, common-layer erasures:', *check_rectangles())
    print('weighted relations and sampled triples:', *simultaneous_collisions())
