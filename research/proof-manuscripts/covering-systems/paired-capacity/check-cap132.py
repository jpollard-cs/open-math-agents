"""Independently verify the ten exclusions by testing every residue of their periods."""
import json
from math import lcm
from pathlib import Path

examples = json.loads(Path(__file__).with_name('cap132-partial.json').read_text())
assert len(examples) == len({tuple(e['ordinary_candidate']) for e in examples}) == 10
for example in examples:
    candidate = set(example['ordinary_candidate'])
    rows = dict(example['cover'])
    assert len(candidate) == 38 and {112,120,126} <= candidate
    assert set(rows) <= candidate and len(rows) == len(example['cover'])
    period = lcm(*rows)
    assert all(any(x % n == a for n,a in rows.items()) for x in range(period))
print('Ten distinct ordinary candidates contain covers, checked throughout every period.')
