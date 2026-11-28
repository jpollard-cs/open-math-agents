"""Exact projection over the five residue classes modulo 5."""
from functools import cache
from math import lcm
from itertools import product
import enumerate_covers as general

def undominated(masks):
    largest = []
    for mask in sorted(set(masks), key=int.bit_count, reverse=True):
        if all(mask & old != mask for old in largest):
            largest.append(mask)
    return tuple(largest)

def partitions(items, k):
    if not items:
        if k == 0:
            yield ()
        return
    if not 1 <= k <= len(items):
        return
    a, rest = items[0], items[1:]
    for groups in partitions(rest, k-1):
        yield ((a,), *groups)
    for groups in partitions(rest, k):
        for i in range(k):
            yield groups[:i] + ((a, *groups[i]),) + groups[i+1:]

@cache
def group_masks(group, allowed, period):
    options = [[allowed & mask for mask in general.row_masks(period, d) if mask & allowed] for d in group]
    result = set()
    for choice in product(*options):
        covered = 0
        for mask in choice:
            covered |= mask
        if covered & 1:
            result.add(covered)
    return undominated(result)

@cache
def hole_masks(cofactors, period):
    maximal = set()
    for groups in partitions(cofactors, 5):
        singles = [g[0] for g in groups if len(g)==1]
        # The ordinary classes leave 0 uncovered after translation. In a
        # singleton section its unique class must therefore have residue 0.
        support = general.row_masks(period, lcm(*singles))[0]
        options = [support]
        for group in groups:
            if len(group) > 1:
                allowed = group_masks(group, support, period)
                options = undominated(x & y for x in options for y in allowed)
        maximal.update(options)
    return undominated(maximal)

@cache
def fill(rest, period, holes):
    if not holes:
        return True
    if not rest or sum(period//d for d in rest) < holes.bit_count():
        return False
    # No ordinary residue is zero: zero is the base hole chosen as origin.
    groups = [undominated(mask & holes for mask in general.row_masks(period,d)[1:]) for d in rest]
    capacities = [row[0].bit_count() for row in groups]
    need = holes.bit_count() - sum(capacities)
    if need > 0:
        return False
    idx = min(range(len(rest)), key=lambda i: sum(x.bit_count() >= capacities[i] + need for x in groups[i]))
    next_rest = rest[:idx] + rest[idx+1:]
    for mask in groups[idx]:
        if mask.bit_count() >= need+capacities[idx] and fill(next_rest, period, holes & ~mask):
            return True
    return False

original = general.can_cover
@cache
def reduced(moduli):
    if not moduli or any(d%25==0 for d in moduli):
        return original(moduli)
    five = tuple(d//5 for d in moduli if d%5==0)
    if len(five) <= 5 or 1 in moduli:
        return original(moduli)
    ordinary = tuple(d for d in moduli if d%5)
    if reduced(ordinary):
        return True
    period = lcm(*ordinary, *five)
    # The 7-section contracts first when it is saturated or underfilled.
    for p,power in general.prime_powers(lcm(*moduli)):
        if p == 5:
            continue
        top = [d for d in moduli if d%power==0]
        if len(top)<=p:
            rest=[d for d in moduli if d%power]
            if len(top)==p:
                rest.append(lcm(*(d//p for d in top)))
            return reduced(tuple(sorted(rest)))
    return any(fill(ordinary, period, ((1<<period)-1) ^ allowed) for allowed in hole_masks(five,period))

if __name__ == '__main__':
    from pathlib import Path
    import json,sys
    general.can_cover = reduced
    cap = int(sys.argv[1])
    result = general.enumerate_sets(cap)
    Path(f'section-{cap}.json').write_text(json.dumps(result))
    print(cap,len(result),{k:min(s[-1] for s in result if len(s)==k) for k in sorted(set(map(len,result)))})
