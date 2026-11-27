"""Rebuild the complete lists of templates, then check exact rational LP witnesses."""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import argparse
import json
import subprocess
import tempfile

from color import certify


def maximal_templates():
    with tempfile.TemporaryDirectory() as temp:
        binary = Path(temp) / "templates"
        subprocess.run(["c++", "-std=c++17", "-O3", str(Path(__file__).with_name("templates.cpp")),
                        "-o", str(binary)], check=True)
        lines = subprocess.check_output([str(binary), "6"], text=True).splitlines()
    result = {}
    for line in lines:
        n, mask, *points = map(int, line.split())
        assert n == len(points) and points == sorted(set(points))
        triples = list(combinations(range(n), 3))
        edges = [sum(1 << v for v in (i, j, k)) for i, j, k in triples
                 if points[i] + points[k] == 2 * points[j]]
        assert mask == sum(1 << t for t, (i, j, k) in enumerate(triples)
                           if points[i] + points[k] == 2 * points[j])
        safe = [s for s in range(1 << n) if all(s & e != e for e in edges)]
        result[f"{n},{mask}"] = points, safe
    return result


def witnesses(points, safe):
    from scipy.optimize import linprog
    n = len(points)
    maximal = [s for s in safe if all(s | (1 << i) not in safe for i in range(n) if not s >> i & 1)]
    rows = [[int(s >> i & 1) for i in range(n)] + [-1] for s in maximal]
    opt = linprog([0]*n + [1], A_ub=rows, b_ub=[0]*len(rows), A_eq=[[1]*n + [0]], b_eq=[1])
    assert opt.success
    def rat(x):
        return str(Fraction(float(x)).limit_denominator(10000))
    return {"bound": rat(opt.x[-1]), "weights": list(map(rat, opt.x[:-1])),
            "mixture": {str(s): rat(-v) for s, v in zip(maximal, opt.ineqlin.marginals) if -v > 1e-8}}


def check(points, safe, data):
    weights = list(map(Fraction, data['weights']))
    bound = Fraction(data['bound'])
    mix = {int(s): Fraction(p) for s, p in data['mixture'].items()}
    assert len(weights) == len(points) and min(weights) >= 0 and sum(weights) == 1
    assert set(mix) <= set(safe) and min(mix.values()) >= 0 and sum(mix.values()) == 1
    for s in safe:
        assert sum(w for i, w in enumerate(weights) if s >> i & 1) <= bound
    for i in range(len(points)):
        assert sum(p for s, p in mix.items() if s >> i & 1) >= bound
    return bound


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--generate', action='store_true', help='use SciPy to rebuild the rational witnesses')
    args = parser.parse_args()
    templates = maximal_templates()
    exceptions, stats = certify(9)
    assert len(exceptions) == 24
    for mask in exceptions:
        e = [sum(1 << i for i in t) for h, t in enumerate(combinations(range(9), 3)) if mask >> h & 1]
        safe = [s for s in range(512) if all(s & edge != edge for edge in e)]
        templates[f"9,{mask}"] = list(range(9)), safe  # indices, not coordinates
    print(f'Nine-site search: {stats.misses} cones and {len(exceptions)} exceptional edge patterns.')
    path = Path(__file__).with_name('certificates.json')
    if args.generate:
        data = {key: witnesses(*v) for key, v in templates.items()}
    else:
        data = json.loads(path.read_text())
    assert set(data) == set(templates)
    values = {}
    for key, (points, safe) in templates.items():
        bound = check(points, safe, data[key])
        values.setdefault(len(points), []).append((bound, points, data[key]['weights']))
    if args.generate:
        path.write_text(json.dumps(data, separators=(',', ':'), sort_keys=True) + '\n')
    assert min(item[0] for item in values.pop(9)) >= Fraction(1,2)
    for n, expected in [(3, Fraction(2,3)), (4, Fraction(2,3)),
                        (5, Fraction(4,7)), (6, Fraction(4,7))]:
        assert min(item[0] for item in values[n]) == expected
    for pts, w, wanted in [([0,2,3,4,5,6,8], [1,1,1,2,1,1,1], 4),
                            (list(range(10)), [2,3,4,5,5,6,5,5,4,3], 20)]:
        best = 0
        for mask in range(1 << len(pts)):
            selected = [p for i,p in enumerate(pts) if mask >> i & 1]
            if all(a+c != 2*b for a,b,c in combinations(selected,3)):
                best = max(best, sum(z for i,z in enumerate(w) if mask >> i & 1))
        assert best == wanted
        print(f'Weighted pattern {pts}: exact maximum {best}/{sum(w)}.')
    for n, items in sorted(values.items()):
        v, x, w = min(items)
        print(f'{n} sites: {len(items)} maximal ordered patterns; minimum {v}; example {x}; weights {w}')
