"""Enumerate the covers first appearing at 56 by contracting its seven top classes."""
from itertools import combinations
from math import lcm
from pathlib import Path
import json
import enumerate_covers as general
from section_solver import reduced

def calculate():
    general.can_cover = reduced
    ordinary = general.modulus_pool(55)
    pool = general.modulus_pool(56)
    seven = tuple(d for d in pool if d % 7 == 0)
    assert [n for n in pool if n % 7] == ordinary
    assert len(seven) == 7 and lcm(*(n//7 for n in seven)) == 120 and 120 not in ordinary

    earlier = json.loads(Path('section-55.json').read_text())
    positive = bytearray(1 << len(ordinary))
    position = {d:i for i,d in enumerate(ordinary)}
    for row in earlier:
        positive[sum(1 << position[d] for d in row)] = 1

    expanded = []
    for mask in range(len(positive)):
        if positive[mask]:
            continue
        rest = mask
        while rest:
            bit = rest & -rest
            if positive[mask ^ bit]:
                positive[mask] = 1
                break
            rest ^= bit
        if positive[mask]:
            continue
        row = tuple(d for i,d in enumerate(ordinary) if mask & (1 << i))
        candidate = (*row,120)
        period = lcm(*candidate)
        if sum(period//d for d in candidate) < period:
            continue
        if any(sum(d % power == 0 for d in candidate) < p
               for p,power in general.prime_powers(period)):
            continue
        if reduced(candidate):
            positive[mask] = 1
            expanded.append(sorted((*row,*seven)))
    return earlier + expanded

if __name__ == '__main__':
    out = calculate()
    Path('full-56.json').write_text(json.dumps(out))
    print(len(out),{k:min(s[-1] for s in out if len(s)==k) for k in sorted(set(map(len,out)))})
