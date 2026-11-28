"""Free one-hole placement on finite digit grids. Shapes are integer bit masks."""
from itertools import combinations, product


def bits(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask -= low


def match(rows, capacities):
    """Augment into individual slots. Return an owner (or None) for every row."""
    slots = [[] for _ in capacities]
    slot_digit = []
    for i, cap in enumerate(capacities):
        for _ in range(min(cap, len(rows))):
            slots[i].append(len(slot_digit))
            slot_digit.append(i)
    occupied = {}
    for start in range(len(rows)):
        # Find one alternating path, including when the public input is tall.
        parent = {start: None}
        visited = set()
        queue = [start]
        end = None
        for row in queue:
            for i in bits(rows[row]):
                for slot in slots[i]:
                    if slot in visited:
                        continue
                    visited.add(slot)
                    if slot not in occupied:
                        end = row, slot
                        break
                    nxt = occupied[slot]
                    if nxt not in parent:
                        parent[nxt] = row, slot
                        queue.append(nxt)
                if end is not None:
                    break
            if end is not None:
                break
        while end is not None:
            row, slot = end
            occupied[slot] = row
            end = parent[row]
    owners = [None] * len(rows)
    for slot, row in occupied.items():
        owners[row] = slot_digit[slot]
    return owners


def viable(edges):
    """Vertices from which a directed cycle is reachable."""
    live = (1 << len(edges)) - 1
    while True:
        smaller = sum(1 << i for i in bits(live) if edges[i] & live)
        if smaller == live:
            return live
        live = smaller


def escape(axes, extras):
    """Find a nonzero tuple avoiding assigned axis rows and extra rows."""
    dim = len(axes)
    for disagreements in product(*(tuple(box.items()) for box in extras)):
        banned = [set() for _ in range(dim)]
        for i, a in disagreements:
            banned[i].add(a)
        edges = [0] * dim
        for i, rows in enumerate(axes):
            for a, guard in rows:
                if a not in banned[i]:
                    edges[i] |= guard
        live = viable(edges)
        if not live or any(0 in banned[i] for i in range(dim) if not live >> i & 1):
            continue
        return tuple(next(a for a, guard in axes[i] if a not in banned[i] and guard & live)
                     if live >> i & 1 else 0 for i in range(dim))
    return None


def complete(axes, rows, remaining, placed):
    x = escape(axes, list(placed.values()))
    if x is None:
        result = placed.copy()
        for r in remaining:
            box = {i: 0 for i in bits(rows[r])}
            box[next(iter(box))] = 1
            result[r] = box
        return result
    for r in remaining:
        box = {i: x[i] for i in bits(rows[r])}
        if any(box.values()):
            result = complete(axes, rows, remaining - {r}, {**placed, r: box})
            if result is not None:
                return result
    return None


def one_hole(sizes, rows):
    """Return placements (coordinate-to-label dicts), or None."""
    caps = tuple(p - 1 for p in sizes)
    defect = len(rows) - sum(caps)
    if defect < 0 or any(s == 0 for s in rows):
        return None
    all_indices = set(range(len(rows)))
    for extra in combinations(range(len(rows)), defect):
        representatives = sorted(all_indices.difference(extra))
        for h in range(min(defect, len(representatives)) + 1):
            for marked in combinations(representatives, h):
                for digits in product(*(tuple(bits(rows[r])) for r in marked)):
                    quotas = list(caps)
                    for i in digits:
                        quotas[i] -= 1
                    if min(quotas, default=0) < 0:
                        continue
                    other = sorted(set(representatives).difference(marked))
                    owners = match([rows[r] for r in other], quotas)
                    if None in owners:
                        continue
                    arrows = [0] * len(sizes)
                    for r, i in zip(other, owners):
                        arrows[i] |= rows[r] ^ (1 << i)
                    if viable(arrows):
                        continue
                    assignment = {}
                    axes = [[] for _ in sizes]
                    for r, i in (*zip(marked, digits), *zip(other, owners)):
                        a = len(axes[i]) + 1
                        axes[i].append((a, rows[r] ^ (1 << i)))
                        assignment[r] = {j: a if j == i else 0 for j in bits(rows[r])}
                    finish = complete(axes, rows, set(extra), {})
                    if finish is not None:
                        assignment.update(finish)
                        return [assignment[r] for r in range(len(rows))]
    return None


def nullity_one_covers(sizes, rows):
    """Decide free coverability when row matching nullity is at most one."""
    caps = [p - 1 for p in sizes]
    missed = match(rows, caps).count(None)
    if not missed:
        return False
    if missed > 1:
        raise ValueError("more than one unmatched row")
    circuit = [s for j, s in enumerate(rows)
               if None not in match(rows[:j] + rows[j + 1:], caps)]
    while len(circuit) > 1:
        for i, p in enumerate(sizes):
            bit = 1 << i
            incident = [s for s in circuit if s & bit]
            if len(incident) == p:
                merged = 0
                for s in incident:
                    merged |= s
                circuit = [s for s in circuit if not s & bit] + [merged ^ bit]
                break
        else:
            return False
    return circuit == [0]


def full_period_defect_one(sizes, ordinary):
    """Return an irreducible full-period witness, or None. Defect exactly one."""
    if len(ordinary) != sum(p - 1 for p in sizes) + 1:
        raise ValueError("expected defect one")
    rows = list(ordinary) + [(1 << len(sizes)) - 1]
    caps = [p - 1 for p in sizes]
    for r in range(len(rows)):
        reduced = rows[:r] + rows[r + 1:]
        if match(reduced, caps).count(None) != 1:
            return None
        if nullity_one_covers(sizes, reduced):
            return None
    witness = one_hole(sizes, ordinary)
    return None if witness is None else witness + [dict.fromkeys(range(len(sizes)), 0)]
