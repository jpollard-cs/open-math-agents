"""Check both datasets, the published table, and the constructor at small k."""
import json
from pathlib import Path
from reciprocal import make, check
from enumerate_covers import enumerate_sets
from exact_minima import classify

def tuples(path):
    return {tuple(s) for s in json.loads(Path(path).read_text())}

if __name__ == '__main__':
    independent = classify()
    capped = set(enumerate_sets(36))
    assert capped == {tuple(r['moduli']) for r in independent}
    assert independent == [dict(moduli=tuple(r['moduli']),residues=r['residues'])
                           for r in json.loads(Path('bounded-covers.json').read_text())]
    catalog = tuples('covers-through-47.json')
    assert {s for s in catalog if s[-1] <= 36} == capped
    assert len(catalog) == 741 and len(capped) == 29
    minima = {k:min(s[-1] for s in catalog if len(s)==k) for k in set(map(len,catalog))}
    assert minima == dict(zip(range(5,16), [12,24,36,36,30,30,36,36,36,36,45]))
    for k in range(5,1001):
        check(make(k),k)
    print('Both cap-36 enumerations agree, the table matches the cap-47 dataset, and all 996 constructors pass.')
