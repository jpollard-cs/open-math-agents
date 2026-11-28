"""Exhaustive checks of subcover extraction on small grids; no solver dependencies."""
from itertools import product


def extract(rows, alphabets, pivot):
    active = {i for i, alphabet in enumerate(alphabets) if len(alphabet) > 1}
    rules = {}
    zero = []
    for index, row in enumerate(rows):
        if any(x != -1 and x not in alphabet for x, alphabet in zip(row, alphabets)):
            continue
        support = frozenset(i for i, x in enumerate(row) if x != -1)
        differs = [i for i in support if row[i] != pivot[i]]
        if not differs:
            zero.append((index, support))
        if len(differs) == 1:
            i = differs[0]
            rules.setdefault((i, row[i]), []).append((index, support - {i}))
    cert = []
    while True:
        unblocked = {}
        for i in sorted(active):
            forced = []
            for x in alphabets[i]:
                if x == pivot[i]:
                    continue
                hit = next((index for index, guard in rules.get((i, x), [])
                            if not (guard & active)), None)
                if hit is None:
                    unblocked[i] = x
                    break
                forced.append(hit)
            else:
                cert.extend((index, i) for index in forced)
                active.remove(i)
                break
        else:
            break
    for index, guard in zero:
        if not (guard & active):
            return cert + [(index, None)], None
    return None, tuple(unblocked.get(i, x) for i, x in enumerate(pivot))


def matches(row, point):
    return all(x == -1 or x == a for x, a in zip(row, point))


def checked(rows, alphabets, pivot):
    cert, hole = extract(rows, alphabets, pivot)
    eligible = [r for r in rows if sum(x != -1 and x != a for x, a in zip(r, pivot)) <= 1]
    covered = all(any(matches(r, x) for r in eligible) for x in product(*alphabets))
    assert covered == (cert is not None)
    if cert is None:
        assert not any(matches(r, hole) for r in eligible)
        return 0
    assert all(any(matches(rows[j], x) for j, _ in cert) for x in product(*alphabets))
    for i, alphabet in enumerate(alphabets):
        entries = [rows[j][i] for j, slot in cert if slot == i]
        assert pivot[i] not in entries and len(set(entries)) == len(entries) <= len(alphabet)-1
    assert sum(slot is None for _, slot in cert) == 1
    return 1


def exhaustive():
    cases = covers = 0
    for widths in ((2, 2), (2, 3)):
        alphabets = tuple(tuple(range(w)) for w in widths)
        available = list(product(*(tuple([-1])+a for a in alphabets)))[1:]
        for bits in range(1 << len(available)):
            rows = [r for j, r in enumerate(available) if bits >> j & 1]
            for pivot in product(*alphabets):
                covers += checked(rows, alphabets, pivot)
                cases += 1
    return cases, covers


def diamond():
    alphabets = [(0,1)]*4
    edges = [(0,2),(2,1),(1,3),(3,0),(0,1)]
    rows = [tuple(1 if i == a else int(j == 4) if i == b else -1 for i in range(4))
            for j, (a,b) in enumerate(edges)]
    rows.append((0,0,0,0))
    # No pivot makes a subcover with a single disagreement on the whole grid.
    assert not any(checked(rows, alphabets, p) for p in product(*alphabets))
    # Two boxes suffice with the same assigned rows. Verify the selected
    # subcovers on both boxes and ensure every row is actually needed.
    pooled = set()
    for x in (0,1):
        box = [(x,)] + alphabets[1:]
        p = (x,0,0,0)
        assert checked(rows, box, p)
        pooled.update(j for j, _ in extract(rows, box, p)[0])
    assert pooled == set(range(6))


if __name__ == "__main__":
    print("grid, family and pivot cases; covered by eligible rows:", exhaustive())
    diamond()
    print("binary diamond minimum boxes: 2")
