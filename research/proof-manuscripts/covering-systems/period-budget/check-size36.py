"""Verify the proper-subset certificate and the four independent size-150 lifts."""
import json
from math import lcm
from pathlib import Path

base = Path(__file__).resolve().parent


def read(name):
    return dict(json.loads((base / name).read_text().splitlines()[0]))


def check_cover(rows):
    period = lcm(*rows)
    hit = bytearray(period)
    for d, r in rows.items():
        assert 0 <= r < d
        hit[r::d] = bytes([1]) * (period // d)
    assert all(hit)
    return period


pool96 = set(json.loads((base / 'census31-32.json').read_text())['pool96'])
only_candidate = (pool96 - {2, 3, 4}) | {27, 54, 105, 108}
proper = read('size36-proper-subset.json')
assert len(only_candidate) == 36
assert set(proper) == only_candidate - {56, 63, 80}
print(f'Sole size-36 candidate contains a {len(proper)}-modulus cover, period {check_cover(proper)}.')

new = [25, 50, 75, 100, 150]
assert lcm(*(d // 5 for d in new)) == 60
for old_size, filename in [(30, 'witness30.jsonl'), (31, 'witness31-96.jsonl'),
                           (32, 'witness32-upper108.jsonl'), (33, 'witness33-upper108.jsonl')]:
    rows = read(filename)
    assert len(rows) == old_size and all(d % 25 for d in rows)
    r = rows.pop(60)
    for digit, d in enumerate(new):
        rows[d] = next(x for x in range(d) if x % (d//5) == r % (d//5) and (x//5) % 5 == digit)
    assert len(rows) == old_size + 4 and max(rows) == 150
    print(f'Size {len(rows)}, maximum 150, covering period {check_cover(rows)}.')
