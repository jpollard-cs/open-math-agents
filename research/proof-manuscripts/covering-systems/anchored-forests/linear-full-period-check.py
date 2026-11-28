"""Exact finite checks of the linear full-period transfer. Python 3, standard library."""
from functools import cache
from math import lcm
from pathlib import Path
from runpy import run_path


@cache
def masks(d, period):
    return tuple(sum(1 << x for x in range(r, period, d)) for r in range(d))


@cache
def unions(ds, size):
    if not ds:
        return (0,)
    return tuple({u | m for u in unions(ds[:-1], size) for m in masks(ds[-1], size)})


def test_refine(family, factors):
    size = 1
    for q in factors:
        size *= q

    def feasible(ds):
        return any(h & ~u == 0 for u in unions(tuple(sorted(ds)), size) for h in family)

    frozen = ()
    d = 1
    for q in factors:
        assert not feasible(frozen) and feasible(frozen + (d,))
        d *= q
        t = next(i for i in range(1, q + 1) if feasible(frozen + (d,) * i))
        frozen += (d,) * (t - 1)
    tests = frozen + (size,)
    for i in reversed(range(len(frozen))):
        sub = tests[:i] + tests[i + 1:]
        if feasible(sub):
            tests = sub
    assert tests[-1] == size and len(tests) <= 1 + sum(q - 1 for q in factors)

    # Independent exact decision works downwards from each actual hole mask.
    @cache
    def cover(h, ds):
        if not h:
            return True
        if not ds:
            return False
        return any(cover(h & ~r, ds[1:]) for r in masks(ds[0], size))

    assert any(cover(h, tests) for h in family)
    for i in range(len(tests)):
        assert not any(cover(h, tests[:i] + tests[i+1:]) for h in family)
    if family == ((1 << size) - 1,):
        assert len(tests) == 1 + sum(q - 1 for q in factors)


def abstract_checks():
    count = 0
    # All nonempty families of nonempty subsets on four points.
    for f in range(1, 1 << 15):
        family = tuple(i + 1 for i in range(15) if f & (1 << i))
        test_refine(family, (2, 2))
        count += 1
    for factors in ((2, 3), (3, 2), (2, 2, 2)):
        size = 6 if len(factors) == 2 else 8
        for h in range(1, 1 << size):
            test_refine((h,), factors)
            test_refine(tuple(sorted({h, ((h << 1) % (1 << size)) | (h >> (size-1))})), factors)
            count += 2
    return count


def factor_positions(d):
    result = []
    for p in range(2, d + 1):
        prev = 1
        while d % p == 0:
            result.append((p, prev))
            prev *= p
            d //= p
    return result


def assignment(ds, omitted_points=0):
    """Search actual row residues, up to independent sibling digit permutations."""
    ds = tuple(sorted(ds))
    period = lcm(*ds)
    positions = {d: factor_positions(d) for d in ds}
    row_masks = {d: masks(d, period) for d in ds}
    def visit(i, holes, used):
        if not holes:
            return [(d, 0) for d in ds[i:]]
        if i == len(ds):
            return None
        if holes.bit_count() > sum(max((holes & m).bit_count() for m in row_masks[d])
                                   for d in ds[i:]):
            return None
        d = ds[i]
        candidates = []
        for r in range(d):
            update = used.copy()
            for p, prev in positions[d]:
                key = p, prev, r % prev
                digit = (r // prev) % p
                seen = used.get(key, 0)
                # For the pinned zero hole, every automorphism must also fix zero.
                if omitted_points and r % prev == 0:
                    seen |= 1
                if digit > seen.bit_length():
                    break
                update[key] = seen | (1 << digit)
            else:
                h = holes & ~row_masks[d][r]
                candidates.append((h.bit_count(), r, h, update))
        for _, r, h, update in sorted(candidates, key=lambda v: v[:2]):
            tail = visit(i+1, h, update)
            if tail is not None:
                return [(d, r)] + tail
        return None
    assert omitted_points in (0, 1)
    return visit(0, ((1 << period)-1) ^ omitted_points, {})


def verify_rows(rows):
    ds = [d for d, _ in rows]
    assert len(ds) == len(set(ds))
    P = lcm(*ds)
    assert all(any(x % d == r for d, r in rows) for x in range(P))
    return P


def lift_rows(old, holes, n, L, tests):
    old_binary = L & -L
    t = 2 + len(tests)
    rows = list(old)
    for j in range(1, t+1):
        d = 2*n if j == 1 else old_binary * 2**j
        x = next(x for x in range(d) if x % old_binary == holes[0] % old_binary
                 and (x // old_binary) % 2**j == 2**(j-1)
                 and (j != 1 or x % n == holes[0] % n))
        rows.append((d, x))
    for j, (m, r) in enumerate(tests, 3):
        x = next(x for x in range(r, m*2**j, m) if (x // old_binary) % 2**j == 0)
        rows.append((m * 2**j, x))
    assert verify_rows(rows) == max(d for d, _ in rows) == L * 2**t
    return rows


def seven_sections():
    # Pin the admissible class to zero modulo 20 by translation. Enumerate
    # inclusion-minimal low holes directly on Z/60, before taking seven lifts.
    holes = [(1 << 60) - 1]
    for d in (2, 3, 4, 5, 6, 10, 15):
        candidates = sorted({h & ~m for h in holes for m in masks(d, 60)},
                            key=int.bit_count)
        holes = []
        for c in candidates:
            if not any((c & h) == h for h in holes):
                holes.append(c)
    allowed = masks(20, 60)[0]
    best = 8
    for h in holes:
        assert h & ~allowed
        # Every 7-section needs one of seven rows to cover an outside hole.
        # The seven rows therefore own separate sections, in arbitrary order.
        nonempty = 0
        for d in (3, 4, 5, 12, 15, 20, 30):
            residuals = [h & ~m for m in masks(d, 60)]
            if not any((v & ~allowed) == 0 for v in residuals):
                break
            nonempty += 0 not in residuals
        else:
            best = min(best, nonempty)
    assert best == 4
    print("inclusion-minimal low masks and minimum occupied seven-sections:", len(holes), best)


def integer_checks():
    ds = (2, 3, 4, 5, 6, 10, 15, 20, 30)
    assert verify_rows(assignment(ds)) == 60 and 60 not in ds
    for d in ds:
        assert assignment(tuple(x for x in ds if x != d)) is None
    A = tuple(d for d in ds if d != 20)
    old = assignment(A, omitted_points=1)
    assert old and all(r != 0 for d, r in old)
    rows = lift_rows(old, [0], 20, 60, [(60,0)])
    for skip, _ in rows:
        assert assignment(tuple(d for d, r in rows if d != skip)) is None
    print("source and lift deletion decisions:", len(ds), len(rows))
    print("lift with full period 480:", rows)

    source = run_path(str(Path(__file__).with_name("prime-position-sieve-check.py")))["example"]()
    old = [(d, r) for d, r in source if d != 20]
    holes = [x for x in range(420) if all(x % d != r for d, r in old)]
    assert holes == [40,100,160,340] and len({x % 140 for x in holes}) == 4
    tests = [(140, x % 140) for x in holes[:3]] + [(420, holes[-1])]
    rows = lift_rows(old, holes, 20, 420, tests)
    print("multiple-hole example, size and period:", len(rows), verify_rows(rows))


if __name__ == "__main__":
    integer_checks()
    seven_sections()
    print("admissible family and chain tests:", abstract_checks())
