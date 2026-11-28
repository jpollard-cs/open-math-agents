"""Construct integer witnesses; independently exhaust finite residue assignments on trees."""
from collections import Counter
from dataclasses import dataclass, field
from itertools import combinations, product
from math import gcd, lcm
from pathlib import Path
import json


@dataclass
class Node:
    p: int
    a: int
    children: list = field(default_factory=list)  # (number of excluded parent values, Node)


def parameters(x):
    unary = x.p - x.a - sum(v for v, _ in x.children)
    assert x.a >= 1 and unary >= 0
    return unary, [(v, (v + 1)*y.a-1, y) for v, y in x.children]


def crt(a, p, b, q):
    assert gcd(p, q) == 1
    return (a + p * ((b-a)*pow(p, -1, q) % q)) % (p*q)


def internal(root):
    """Use 0 as the marked digit at each vertex, and leave 0..a-1 feasible."""
    unary, edges = parameters(root)
    rows = [(root.p, root.a+i) for i in range(unary)]
    first = root.a + unary
    period = root.p
    for v, t, y in edges:
        child_period, child_rows = internal(y)
        period *= child_period
        rows.extend(child_rows)
        fixed = [(i, j) for i in range(first, first+v) for j in range(y.a)]
        fixed.extend((0, j) for j in range(1, y.a))
        assert len(fixed) == t
        rows.extend((root.p*y.p, crt(i, root.p, j, y.p)) for i, j in fixed)
        first += v
    return period, rows


def star_example():
    root = Node(3,1,[(1,Node(5,2)),(1,Node(7,2))])
    q, rows = internal(root)
    usable = [x for x in range(q) if all(x%n != r for n,r in rows)]
    assert usable == [0]
    counter = Counter()
    ordinary = [(2**j, 2**(j-1)) for j in range(1,5)]
    for n, a in rows:
        d = 2**counter[n]
        counter[n] += 1
        ordinary.append((n*d, crt(a,n,0,d)))
    L = 16*q
    assert len({n for n,_ in ordinary}) == len(ordinary)
    assert [x for x in range(L) if all(x%n != r for n,r in ordinary)] == [0]
    # Close the distinguished row with the fresh prime 11.
    divisors = [1,2,3,4,5,6,7,8,10,12,16]
    assert lcm(*divisors) == L
    cover = ordinary + [(11*d, L*i % (11*d)) for i,d in enumerate(divisors)]
    assert len(cover) == len(set(n for n,_ in cover)) == 29
    period = lcm(*(n for n,_ in cover))
    assert all(any(x%n == a for n,a in cover) for x in range(period))
    print('Integer example:',len(cover),'distinct moduli, maximum',max(n for n,_ in cover),
          'period',period,'full coverage. Before closure the unique hole is 0 modulo',L)
    return ordinary, cover


def multiset_masks(alphabet, count):
    """For a lower bound on holes, repeated hits can be completed to distinct hits."""
    assert 0 <= count <= alphabet
    return combinations(range(alphabet), count)


def orbit_profiles(raw, delete=None):
    """Direct enumeration of forbidden cells, independent of the row-allocation inequalities.

    Keep only the multiset of numbers of subtree completions (clipped at two).
    Permutations of a digit alphabet act on every assignment, so a child multiset
    can be matched with any labels on its incoming edge.
    """
    p = raw.p
    unaries, edges = parameters(raw)
    if delete == ('unary',p):
        assert unaries
        unaries -= 1
    profiles = {(1,)*p}
    for v,t,child in edges:
        if delete == ('edge',p,child.p):
            t -= 1
        child_profiles = orbit_profiles(child, delete)
        local = set()
        width = child.p
        for child_vector in child_profiles:
            total = sum(child_vector)
            for pairs in multiset_masks(p*width,t):
                removed = [0]*p
                for i in pairs:
                    x,y = divmod(i,width)
                    removed[x] += child_vector[y]
                local.add(tuple(min(2,total-n) for n in removed))
        # local already contains every permutation of a profile. Hence fix the
        # representative on the accumulated side and sort only after multiplication.
        profiles = {tuple(sorted(min(2,a*b) for a,b in zip(old,leg)))
                    for old in profiles for leg in local}
    return {tuple(sorted(0 if j in banned else n for j,n in enumerate(old)))
            for old in profiles for banned in multiset_masks(p,unaries)}


def deletion_types(x):
    u, edges = parameters(x)
    if u:
        yield ('unary',x.p)
    for v,t,y in edges:
        yield ('edge',x.p,y.p)
        yield from deletion_types(y)


def check_tree(tree):
    period, rows = internal(tree)
    holes = [v for v in range(period) if all(v%n != a for n,a in rows)]
    assert tree.a == 1 and holes == [0]
    counts = {}
    for delete in [None,*deletion_types(tree)]:
        profiles = orbit_profiles(tree, delete)
        least = min(sum(v) for v in profiles)
        assert (least==1 if delete is None else least>=2)
        counts[str(delete)] = least
    print('Independent residue enumeration:',period,'internal positions,',len(rows),
          'ordinary rows, least clipped hole counts',counts)
    return counts


def prime_sieve(n):
    bits = bytearray([1])*(n+1)
    bits[:2] = bytes(2)
    for i in range(2,n+1):
        if bits[i]:
            if i*i <= n:
                bits[i*i::i] = bytes((n-i*i)//i+1)
            yield i


def cap_plan(z, parent_children, a):
    """Check a finite star schedule without constructing the huge final residue period."""
    ps = list(prime_sieve(z))
    assert z==ps[-1] and z>=7
    chosen = {p for p,_ in parent_children}
    right = {q for _,group in parent_children for q in group}
    assert not chosen & right and chosen|right <= set(ps[:-1])
    assert sum(len(g) for _,g in parent_children)==len(right)
    assert all(0<len(group)<p for p,group in parent_children)
    old = 1
    rows = set()
    # All permanent rows before the terminal step divide the new period and
    # contain the newly introduced digit. Cross-step distinctness also checked here.
    cap = z*(z+1)
    def ordinary(r,j):
        nonlocal old
        n = r**j
        ds = []
        for d in range(1,cap//n+1):
            if old%d==0 and d%r:
                ds.append(d)
                if len(ds)==r-1:
                    break
        assert len(ds)==r-1
        fixed = [n*d for d in ds]
        assert all(n0//gcd(n0,old)==r and n0 not in rows for n0 in fixed)
        rows.update(fixed)
        old *= r
    def powers(r):
        n,j = r,1
        while n<=z+1:
            yield j
            n*=r
            j+=1
    def raw(group,n,needed):
        ds=[]
        for d in range(1,cap//n+1):
            if group%d==0:
                ds.append(d)
                if len(ds)==needed:
                    break
        if not needed:
            return
        assert len(ds)==needed
        fixed=[d*n for d in ds]
        assert all(x not in rows for x in fixed)
        rows.update(fixed)
    stop = max(right)
    for r in ps:
        if r>stop:
            break
        if r not in chosen|right:
            for j in powers(r):
                ordinary(r,j)
    before = old
    gain = 0
    for p,g in parent_children:
        raw(before,p,p-1-len(g))
        old*=p
        for q in g:
            b = a[q]
            assert 1<=b<=q
            raw(before,q,q-b)
            raw(before,p*q,2*b-1)
            old*=q
            gain+=b-1
    for r in ps[:-1]:
        for j in powers(r):
            if (r in chosen|right and j>1) or r>stop:
                ordinary(r,j)
    ds=[*range(1,z),z+1]
    assert lcm(*ds)==old and len(ds)==z
    assert not rows & {z*d for d in ds}
    rows.update(z*d for d in ds)
    baseline=1+sum(r-1 for r in ps for _ in powers(r))
    assert max(rows)==cap and len(rows)==baseline+gain
    return len(rows),gain,cap


def main():
    ordinary,cover = star_example()
    examples=[
        Node(3,1,[(1,Node(5,2)),(1,Node(7,2))]),
        Node(3,1,[(1,Node(5,2,[(1,Node(2,2))]))]),
        Node(5,1,[(2,Node(3,2)),(1,Node(2,1))])]
    checks=[check_tree(t) for t in examples]
    group=[(5,[17,19]),(7,[23,29,31])]
    for z in (97,149,251):
        first=None
        for target in range(21):
            left=target
            heights={}
            for _,g in group:
                for q in g:
                    step=min(left,4)
                    heights[q]=1+step
                    left-=step
            size,gain,cap=cap_plan(z,group,heights)
            assert gain==target
            if first is None: first=size
            assert size==first+target
        print('Finite exact-size schedules:',z,'size',first,'through',size,'cap',cap)
    data={'ordinary_before_closure':ordinary,'residues':sorted(cover),'independent_minima':checks}
    Path(__file__).with_name('example29.json').write_text(json.dumps(data,indent=2)+'\n')


if __name__=='__main__':
    main()
