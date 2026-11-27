"""Independent finite check of the multiple-hole example, using only Python."""
from functools import cache
from math import lcm


def row(d, a):
    return sum(1 << x for x in range(a, 60, d))


FULL = (1 << 60) - 1
LOW = (2, 3, 4, 6, 5, 10, 15)  # delete 20 from the ordinary rows
COF = (3, 4, 5, 12, 15, 20, 30)
ALL = (1 << len(COF)) - 1
INF = 421


def minimal(masks):
    kept = []
    for h in sorted(set(masks), key=int.bit_count):
        if all((m & h) != m for m in kept):
            kept.append(h)
    return kept


@cache
def section(h, mask):
    if not mask:
        return INF if h & ~row(20, 0) else h.bit_count()
    bit = mask & -mask
    d = COF[bit.bit_length() - 1]
    return min(section(h & ~row(d, a), mask ^ bit) for a in range(d))


@cache
def split(h, mask, parts):
    if parts == 1:
        return section(h, mask)
    best = INF
    sub = mask
    while True:
        local = section(h, sub)
        if local < best:
            best = min(best, local + split(h, mask ^ sub, parts - 1))
        if sub == 0:
            return best
        sub = (sub - 1) & mask


def main():
    holes = [FULL]
    for d in LOW:
        holes = minimal(h & ~row(d, a) for h in holes for a in range(d))
    assert all(lcm(*(d for d in COF if d != skipped)) == 60 for skipped in COF)
    # Translate the putative common residue modulo 20 to zero.
    optimum = min(split(h, ALL, 7) for h in holes)
    print("inclusion-minimal ordinary masks", len(holes))
    print("minimum holes in one 20-class after deleting 20", optimum)
    assert optimum == 4

    # Independent direct witness, using CRT by enumeration of one period.
    seed = list(zip(LOW, (1, 0, 2, 2, 1, 2, 4)))
    for section_id, d in enumerate(COF):
        residue = next(x for x in range(7*d) if x % 7 == section_id and (x-28) % d == 0)
        seed.append((7*d, residue))
    def misses(x, rows):
        return all(x % d != r for d, r in rows)
    private = [x for x in range(420) if misses(x, seed)]
    assert len(private) == 4 and all(x % 20 == 0 for x in private)
    extended = seed.copy()
    for j in range(1, 7):
        d = 40 if j == 1 else 4 * 2**j
        r = next(x for x in range(d) if x % (4 * 2**j) == 4 * 2**(j-1)
                 and (j != 1 or x % 20 == 0))
        extended.append((d, r))
    for j, hole in enumerate(private, 3):
        d = 420 * 2**j
        r = next(x for x in range(hole, d, 420) if x % (4 * 2**j) == 0)
        extended.append((d, r))
    ds = [d for d, _ in extended]
    assert len(ds) == len(set(ds)) == 24 and max(ds) == lcm(*ds) == 26880
    assert not any(misses(x, extended) for x in range(lcm(*ds)))
    print("base holes", private, "lifted size and period", len(ds), lcm(*ds))


if __name__ == "__main__":
    main()
