"""Independent exhaustive classification with largest modulus at most 36."""
from collections import Counter
from functools import cache
from itertools import combinations
from math import lcm
import json

# Full prime powers in the period satisfy (p+1)*p**a <= 36.
POOL = tuple(n for n in range(2, 37) if 360 % n == 0)
FIVES = (5, 10, 15, 20, 30)

@cache
def base_witness(moduli):
    """Return a covering residue tuple, or None. Repeated moduli are allowed."""
    period = lcm(*moduli)
    if sum(period // n for n in moduli) < period:
        return None
    classes = [[sum(1 << x for x in range(a, period, n)) for a in range(n)]
               for n in moduli]

    @cache
    def fill(i, holes):
        if holes == 0:
            return (0,) * (len(moduli) - i)
        if i == len(moduli):
            return None
        gains = [max((holes & mask).bit_count() for mask in row) for row in classes[i:]]
        if sum(gains) < holes.bit_count():
            return None
        residues = range(1) if i == 0 else range(moduli[i])
        for a in residues:
            rest = fill(i + 1, holes & ~classes[i][a])
            if rest is not None:
                return (a, *rest)
        return None

    return fill(0, (1 << period) - 1)

def witness(moduli):
    ordinary = tuple(n for n in moduli if n % 5)
    top = tuple(n for n in moduli if n % 5 == 0)
    # Work in Z/72 times Z/5. With fewer than five rows one fibre is empty.
    # With all five, every base hole lies in the intersection of five single
    # classes, hence in a single class mod lcm(1,2,3,4,6)=12.
    use_all = top == FIVES
    reduced = tuple(sorted(ordinary + ((12,) if use_all else ())))
    residues = base_witness(reduced)
    if residues is None:
        return None
    pairs = list(zip(reduced, residues))
    lifts = {}
    if use_all:
        idx = next(i for i,(d,_) in enumerate(pairs) if d == 12)
        _, hole = pairs.pop(idx)
        for digit, n in enumerate(top):
            lifts[n] = next(x for x in range(n) if x % 5 == digit and (x-hole) % (n//5) == 0)
    else:
        lifts = dict.fromkeys(top, 0)
    lifts.update(pairs)
    return [lifts[n] for n in moduli]

def classify():
    covers = set()
    minimal = []
    for k in range(1, len(POOL) + 1):
        for moduli in combinations(POOL, k):
            residues = witness(moduli)
            if residues is None:
                continue
            covers.add(moduli)
            if any(moduli[:i] + moduli[i+1:] in covers for i in range(k)):
                continue
            assert all(any((x-a) % n == 0 for n,a in zip(moduli, residues)) for x in range(360))
            minimal.append(dict(moduli=moduli, residues=residues))
    return minimal

if __name__ == '__main__':
    rows = classify()
    for k in sorted({len(row['moduli']) for row in rows}):
        print(k, min(row['moduli'][-1] for row in rows if len(row['moduli'])==k))
    print('Irreducible sets:', len(rows))
    with open('bounded-covers.json', 'w') as f:
        json.dump(rows, f, indent=1)
