"""Direct integer residue and projection checks. Python 3.10+."""
from collections import Counter, defaultdict
from functools import cache
from itertools import product
from math import lcm, prod


@cache
def masks(period, n):
    return tuple(sum(1 << j for j in range(a, period, n)) for a in range(n))


def covers(period, moduli):
    @cache
    def search(holes, remaining):
        if not holes:
            return True
        if sum(period // n for n in remaining) < holes.bit_count():
            return False
        x = (holes & -holes).bit_length() - 1
        for i,n in enumerate(remaining):
            if search(holes & ~masks(period, n)[x % n], remaining[:i] + remaining[i+1:]):
                return True
        return False
    return search((1 << period) - 1, tuple(sorted(moduli)))


@cache
def patterns(period, digits):
    groups = defaultdict(int)
    for x in range(period):
        key = tuple(x // (p**(j-1)) % p for p,j in digits)
        groups[key] |= 1 << x
    return tuple(groups.values())


@cache
def unions(period, earlier):
    if not earlier:
        return frozenset([0])
    return frozenset(old | extra for old in unions(period, earlier[:-1])
                     for extra in masks(period, earlier[-1]))


@cache
def visible(period, earlier, digits):
    classes = patterns(period, digits)
    return min(sum((mask & ~old) != 0 for mask in classes) for old in unions(period, earlier))


def check(moduli, digits):
    period = lcm(*moduli)
    assert covers(period, moduli)
    assert all(not covers(period, moduli[:i]+moduli[i+1:]) for i in range(len(moduli)))
    supports = {n: {i for i,(p,j) in enumerate(digits) if n % p**j == 0} for n in moduli}
    counts = Counter()
    for levels in product(range(len(digits)), repeat=len(digits)):
        if set(levels) != set(range(max(levels)+1)):
            continue
        for reserved in moduli:
            stage = {n: max(levels[i] for i in support) for n,support in supports.items() if n != reserved}
            groups = defaultdict(list)
            for n,t in stage.items():
                internal = tuple(i for i in sorted(supports[n]) if levels[i] == t)
                groups[t,internal].append(n)
            counts["orders_and_reservations"] += 1
            for (t,internal), rows in groups.items():
                old = tuple(sorted(n for n,s in stage.items() if s<t))
                guards = {i for n in rows for i in supports[n] if levels[i]<t}
                b = visible(period, old, tuple(digits[i] for i in sorted(guards)))
                P = prod(digits[i][0] for i in internal)
                least_multiple = lcm(*(digits[i][0]**digits[i][1] for i in internal))
                assert len(rows) < b*P
                assert len(rows) <= max(moduli)//least_multiple
                counts["groups"] += 1
                counts["several_old_patterns"] += int(b>1)
                counts["tight_capacity"] += int(len(rows)==b*P-1)
    return counts


if __name__ == "__main__":
    total = Counter()
    for D, digits in [
        ((2,3,4,6,12), ((2,1),(2,2),(3,1))),
        ((2,3,4,6,8,24), ((2,1),(2,2),(2,3),(3,1))),
        ((2,3,4,6,9,18,36), ((2,1),(2,2),(3,1),(3,2))),
        ((2,3,4,5,6,10,15,20,30), ((2,1),(2,2),(3,1),(5,1))),
    ]:
        counts = check(D, digits)
        total += counts
        print("period", lcm(*D), "largest", max(D), dict(counts), flush=True)
    print("combined", dict(total))
