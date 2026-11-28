"""Finite checks of the weighted extraction, fixed-cofactor slicing, and cap accounting."""
from bisect import bisect_right
from fractions import Fraction as F
from itertools import combinations, product
from math import lcm, prod


def edge_mass(subset, edges, weight):
    return sum(weight[i]*weight[j] for i,j in edges if subset >> i & subset >> j & 1)


def graph_checks():
    checked_graphs = checked_cuts = erasures = 0
    vertices = 6
    pairs = tuple(product(range(3), range(3,6)))
    for weights in [(1,1,1,1,1,1), (1,4,7,3,8,2), (12,18,9,5,2,1)]:
        # Integer vertex weights are equivalent to rational weights by common scaling.
        W = [sum(x for i,x in enumerate(weights) if mask>>i & 1) for mask in range(1<<vertices)]
        M = W[-1]
        for mask in range(1, 1<<len(pairs)):
            edges = [edge for i,edge in enumerate(pairs) if mask>>i & 1]
            E = [edge_mass(U, edges, weights) for U in range(1<<vertices)]
            D = F(E[-1], 2*M)
            a = D/8
            h = min(D-2*a, 2*D*a/M)
            H = min((u for u in range(1<<vertices) if W[u]>=2*a and E[u]>D*(W[u]-a)),
                    key=int.bit_count)
            for u in range(1<<vertices):
                if u & ~H or W[u] > h/4:
                    continue
                if u:
                    erasures += 1
                left = H ^ u
                for i in range(vertices):
                    if left>>i & 1:
                        neighbors = {y for x,y in edges if x==i} | {x for x,y in edges if y==i}
                        assert sum(weights[j] for j in neighbors if left>>j & 1) > D-W[u]
                side = left
                while side:
                    comp = left ^ side
                    if comp:
                        crossing = E[left]-E[side]-E[comp]
                        assert crossing >= (h-W[u])*min(W[side],W[comp])
                        checked_cuts += 1
                    side = (side-1) & left
            checked_graphs += 1
    # Exact nonempty erasures on complete bipartite graphs with one small atom.
    for n in (1000,2000,3000):
        # Same four-cell-weight computation tests every cut on both sides after deletion.
        weights = (1,n,n,n)
        edges = tuple(product((0,1),(2,3)))
        M = sum(weights)
        D = F(edge_mass(15,edges,weights), 2*M)
        h = min(3*D/4, D*D/(4*M))
        assert 1 <= h/4
        for side in (2,4,6,8,10,12):
            other = 14 ^ side
            left = sum(x for i,x in enumerate(weights) if side>>i & 1)
            right = sum(x for i,x in enumerate(weights) if other>>i & 1)
            assert edge_mass(14,edges,weights)-edge_mass(side,edges,weights)-edge_mass(other,edges,weights) >= (h-1)*min(left,right)
            checked_cuts += 1
        erasures += 1
    return checked_graphs, checked_cuts, erasures


def primes_through(limit):
    prime = bytearray(b'\1') * (limit+1)
    prime[:2] = b'\0\0'
    for p in range(2, int(limit**.5)+1):
        if prime[p]:
            prime[p*p::p] = bytes(1+(limit-p*p)//p)
    return [i for i in range(limit+1) if prime[i]]


def arithmetic_checks():
    primes = primes_through(500)
    grids = 0
    powers = [(p,j) for p in primes[:5] for j in range(1,4)]
    for size in (2,3,4,5):
        for group in combinations(powers,size):
            p,j = min(group)
            m = lcm(*(q**l for q,l in group))
            P = prod(q for q,_ in group)
            assert m >= P and m >= p**(j+1)
            if size >= 3 or (len({q for q,_ in group})==2 and max(l for q,l in group)>1):
                assert m >= p**3
            for X in (4*p*p, 13*p**3):
                for B in (1,3,14):
                    count = min(B*P-1, X//m)
                    assert count**2 <= B*X
                    if size >= 3:
                        assert count <= X//p**3
            grids += 1
    # Exact maximization over all subsets of fixed cardinality in a short prime list.
    neighbors = 0
    for p in primes[:24]:
        start = bisect_right(primes,p)
        pool = primes[start:start+9]
        for h in range(1,6):
            best = sum(F(1,q) for q in pool[:h])
            for choice in combinations(pool,h):
                assert sum(F(1,q) for q in choice) <= best
                neighbors += 1
    return grids, neighbors


def layer_checks():
    # Compute intersections directly and via edge occurrence probabilities, with repeated draws.
    edge_weights = (F(1,33),F(1,39),F(1,55),F(1,65))
    ds = (2,3,5)
    masses = tuple(F(1,d) for d in ds)
    denominator = sum(masses)
    tested = 0
    for layers in product((3,5,7,9,13,14,15), repeat=3):
        for r in (2,3):
            direct = F(0)
            for draws in product(range(3),repeat=r):
                mask = 15
                for i in draws:
                    mask &= layers[i]
                direct += prod(masses[i]/denominator for i in draws)*sum(w for j,w in enumerate(edge_weights) if mask>>j & 1)
            probs = [sum(m for m,layer in zip(masses,layers) if layer>>j & 1)/denominator for j in range(4)]
            moment = sum(w*f**r for w,f in zip(edge_weights,probs))
            assert direct == moment
            assert moment*sum(edge_weights)**(r-1) >= sum(w*f for w,f in zip(edge_weights,probs))**r
            tested += 1
    return tested


if __name__ == '__main__':
    print("Weighted graphs, cuts and nonempty erasure trials:", graph_checks())
    print("Mixed supports and extremal prime neighbor comparisons:", arithmetic_checks())
    print("Weighted cofactor intersections:", layer_checks())
