"""Check donor batches, stage certificates, and the weighted accounting, Python 3."""
from itertools import product
from math import gcd, lcm, prod


def finite_cover():
    old_divisors = sorted(x for x in range(1,201) if 200 % x == 0)
    stages = [(2,[2]),(2,[4]),(2,[8]),(5,[5,10,20,40]),(5,[25,50,100,200]),
              (11,[11*d for d in old_divisors[:10]]),
              (13,[13*d for d in old_divisors[:12]]),(3,[33,39]),
              (17,[17*d for d in (1,2,4,5,8,10,11,13,20,25,40,50,100,200,3,6,15)])]
    old = 1
    assignment = {}
    for j, (radix, rows) in enumerate(stages):
        final = j == len(stages)-1
        assert len(rows) == radix - 1 + final
        assert all(lcm(old,n) == old*radix for n in rows)
        if final:
            assert lcm(*(gcd(old,n) for n in rows)) == old
        for i,n in enumerate(rows):
            assert n not in assignment
            assignment[n] = old*(i+1) % n
        old *= radix
    assert (len(assignment),max(assignment),old) == (52,3400,1458600)
    masks = {11:set(stages[5][1]+[33]),13:set(stages[6][1]+[39])}
    assert not masks[11] & masks[13]
    coverage = bytearray(old)
    for n,a in assignment.items():
        coverage[a::n] = bytes([1])*(old//n)
    assert all(coverage)
    cases = {}
    for reserved in assignment:
        live = tuple(p for p,rows in masks.items() if reserved not in rows)
        removed = {reserved}.union(*(masks[p] for p in live))
        # Cache equal exclusions, and count projections by scanning actual integers.
        key = frozenset(removed)
        if key not in cases:
            remaining = bytearray(old)
            for n,a in assignment.items():
                if n not in removed:
                    remaining[a::n] = bytes([1])*(old//n)
            for p in live:
                guard = lcm(*(n//p for n in masks[p]))
                seen = {x % guard for x in range(old) if not remaining[x]}
                assert {a % 3 for a in seen} == {0,1,2}
                if reserved not in {2,4,8,5,10,20,40,25,50,100,200}:
                    assert len(seen)==3
            cases[key] = True
    return len(assignment)


def independent_joint_model():
    # All complement placements in a small two-coordinate test. An intact
    # recipient has no own constraints and can disable its marked terminal
    # guard. A broken recipient has at most radix-1 constraints total,
    # one of which may also test the donor label.
    checked = 0
    for first, second, marked, reserved_label in product(range(3),range(3),range(2),range(2)):
        for donor_labels in product(range(2), repeat=2):
            for g in range(2):
                assert any(p0 != marked and p1 != first and
                           (p1 != second or g != donor_labels[0])
                           for p0,p1 in product(range(2),range(3)))
            # Keep terminal and donor labels arbitrary too, and test full extensions.
            for g in range(2):
                assert any(p1 != first and (p1 != second or g != donor_labels[0]) and
                           (p0 != marked or z != reserved_label) and z != donor_labels[1]
                           for p0,p1,z in product(range(2),range(3),range(2)))
            checked += 1
    return checked


def excess_identity():
    from fractions import Fraction
    counts = 0
    for q in (2,3,5,7,11,13,17,19):
        for n in range(8*q+1):
            for erased in range(n+1):
                w=n-erased
                h=w//q
                e=max(0,w-q+1)
                if h:
                    assert Fraction(e,h) <= q
                    assert h*Fraction(e,h) == e
                else:
                    assert e==0
                assert n<=erased+(q-1)+e
                counts += 1
    return counts


if __name__=='__main__':
    print('52-modulus example: reservations checked',finite_cover())
    print('Independent small assignment tests',independent_joint_model())
    print('Exact post-erasure excess identities',excess_identity())
