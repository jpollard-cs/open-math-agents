"""Independent tests of the overfilled fibre theorem and a small ordinary cover."""
from itertools import product, combinations_with_replacement
from math import lcm
from saturated_boxes import crt


def profiles(b, a, t):
    """All activations of right colours on one left digit, up to row order."""
    result = set()
    for rows in combinations_with_replacement(range(a*b), t):
        active = [0]*b
        for row in rows:
            left, right = divmod(row, a)
            active[left] |= 1 << right
        result.add(tuple(active))
    return result


def check_hub(left, a, mult, target, u=None):
    domains = [range(b) for b in left]
    points = list(product(*domains))
    full = (1 << a)-1
    possibilities = [profiles(b, a, t) for b, t in zip(left, mult)]
    best = total = exact = 0
    masks = set()
    for fixed, varying in product(*possibilities):
        missed = [a - (fixed[i] | varying[j]).bit_count() for i, j in points]
        killed = [i for i, n in enumerate(missed) if n == 0]
        masks.add(sum(1 << i for i in killed))
        assert max(fixed) <= full and max(varying) <= full
        total += 1
        best = max(best, len(killed))
        if u is None or len(killed) != target:
            continue
        exact += 1
        varying_axes = [axis for axis in range(2)
                        if len({points[j][axis] for j in killed}) > 1]
        assert len(varying_axes) == 1
        var = varying_axes[0]
        anchor = points[killed[0]]
        values = {points[j][var] for j in killed}
        for x, holes in zip(points, missed):
            expect = mult[1-var]*int(x[1-var] != anchor[1-var]) + u*int(x[var] not in values)
            assert holes == expect
    assert best == target
    return total, exact, masks


def check_profiles():
    tests = [((2,2),3,(2,2),2,1), ((3,2),3,(2,2),2,1),
             ((2,3),3,(2,2),2,1), ((2,2),4,(2,2),1,None),
             ((2,2),3,(1,2),1,None), ((2,2),3,(2,1),1,None),
             ((2,2),6,(4,4),2,2)]
    total = tight = 0
    for left, a, mult, target, u in tests:
        n, exact, masks = check_hub(left, a, mult, target, u)
        total += n
        tight += exact
        full = (1 << (left[0]*left[1]))-1
        if mult == (2,2) and a == 3:
            assert any(x | y == full for x in masks for y in masks) == (left==(2,2))
        print('left',left,'right values',a,'rows',mult,'maximum',target,'profiles',n)
    print(total, 'distinct pairs of activation profiles checked;', tight, 'tight profiles audited.')


def check_integers():
    # Each of the two segments varies the first coordinate, at second digit 0 or 1.
    left = (3, 5)
    right = (7, 11)
    raw = []
    for p in left:
        for j in range(p-2):
            raw.append((p, 2+j, 2**j, None))
    for owner, q in enumerate(right):
        for j in range(q-6):
            raw.append((q, 6+j, 2**j, q))
        for j in range(4):
            raw.append((5*q, crt(owner,5,j,q), 2**j, q))
            raw.append((3*q, crt(j//2,3,4+j%2,q), 2**j, q))
    ext = lcm(*(d for _,_,d,_ in raw))
    assert ext == 16
    side = [(2**j,2**(j-1),None) for j in range(1,5)]
    rows = side + [(d*n,crt(0,d,r,n),q) for n,r,d,q in raw]
    assert len({n for n,_,_ in rows}) == len(rows)
    period = lcm(*(n for n,_,_ in rows))
    private = [set() for _ in rows]
    for x in range(period):
        hit = [i for i,(n,r,q) in enumerate(rows) if x%n == r]
        assert hit
        if len(hit)==1:
            private[hit[0]].add(x)
    assert all(private)
    for (n,r,owner), sites in zip(rows[len(side):], private[len(side):]):
        for q in right:
            if q != owner:
                assert len({x % q for x in sites}) >= 2
    print(len(rows),'distinct moduli, maximum',max(n for n,_,_ in rows),
          'period',period,'least private count',min(map(len, private)),
          'and the right-prime projections of all packet rows audited.')
    return [(n,r) for n,r,_ in rows]


if __name__=='__main__':
    check_profiles()
    check_integers()
