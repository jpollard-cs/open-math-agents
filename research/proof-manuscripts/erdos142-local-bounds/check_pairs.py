"""Check the pair-marginal certificates with standard Python and a C++17 compiler.

Run python check_pairs.py from any directory. C++ enumerates patterns up to
seven sites; every subsequent test uses integers, including all moment sums.
"""

from itertools import combinations, permutations
from pathlib import Path
import subprocess
import tempfile


def require(condition, message):
    if not condition:
        raise ValueError(message)


def bits(vertices):
    return sum(1 << i for i in vertices)


def progression_mask(points):
    triples = combinations(points, 3)
    return sum(1 << j for j, (a, b, c) in enumerate(triples) if a + c == 2 * b)


def forbidden_subsets(size, mask):
    return [bits(t) for j, t in enumerate(combinations(range(size), 3)) if mask >> j & 1]


def admissible(subset, forbidden):
    return all(subset & edge != edge for edge in forbidden)


def maximal_patterns():
    with tempfile.TemporaryDirectory() as folder:
        binary = Path(folder) / "templates"
        source = Path(__file__).with_name("templates.cpp")
        subprocess.run(["c++", "-O3", "-std=c++17", str(source), "-o", str(binary)], check=True)
        rows = subprocess.check_output([str(binary), "7"], text=True)
    result = {n: set() for n in range(3, 8)}
    for row in rows.splitlines():
        n, h, *points = map(int, row.split())
        require(len(points) == n and points == sorted(set(points)), "invalid representative")
        require(progression_mask(points) == h and h not in result[n], "incorrect or duplicate mask")
        result[n].add(h)
    require([len(result[n]) for n in range(3, 8)] == [1, 3, 16, 152, 2238], "template counts")
    return result


def check_upper(points, constant, linear, quadratic, expected):
    n = len(points)
    pairs = list(combinations(range(n), 2))
    require(len(linear) == n and len(quadratic) == len(pairs), "coefficient count")
    forbidden = forbidden_subsets(n, progression_mask(points))
    for subset in range(1 << n):
        if admissible(subset, forbidden):
            z = [(subset >> i) & 1 for i in range(n)]
            value = constant + sum(a * v for a, v in zip(linear, z))
            value += sum(b * z[i] * z[j] for b, (i, j) in zip(quadratic, pairs))
            require(value <= 0, f"upper inequality fails on {points}, subset {subset}")
    require((constant, sum(linear), sum(quadratic)) == expected, "wrong averaged coefficients")


def check_five(patterns):
    # Each integer weight is the number of copies of each listed subset.
    distributions = [
        ((0, 1, 2, 3, 4), [(3, [0]), (6, [3, 10, 17, 24]), (3, [5, 6, 12, 20]),
                            (6, [13, 22]), (3, [27])]),
        ((0, 2, 3, 4, 6), [(4, [1, 4, 16]), (1, [3, 6, 9, 12, 18, 24]),
                            (1, [5, 17, 20]), (4, [7, 13, 19, 22, 25, 28]), (9, [10])]),
    ]
    triples = list(combinations(range(5), 3))
    supersets = set()
    for points, distribution in distributions:
        mask = progression_mask(points)
        forbidden = forbidden_subsets(5, mask)
        for count, subsets in distribution:
            require(count > 0 and all(0 <= s < 32 and admissible(s, forbidden) for s in subsets),
                    "invalid atom of a five-site distribution")
        for degree, expected in enumerate((54, 24, 9)):
            for face in combinations(range(5), degree):
                f = bits(face)
                weight = sum(count for count, subsets in distribution for s in subsets if s & f == f)
                require(weight == expected, "incorrect five-site moment")
        edges = [t for j, t in enumerate(triples) if mask >> j & 1]
        for perm in permutations(range(5)):
            supersets.add(bits(triples.index(tuple(sorted(perm[i] for i in t))) for t in edges))
    require(all(any(h & m == h for m in supersets) for h in patterns), "uncovered five-site pattern")


def check_seven(patterns):
    triples = list(combinations(range(7), 3))
    index = {t: j for j, t in enumerate(triples)}
    lines = [t for t in triples if (t[0]+1) ^ (t[1]+1) ^ (t[2]+1) == 0]
    designs = set()
    for perm in permutations(range(7)):
        designs.add(bits(index[tuple(sorted(perm[i] for i in t))] for t in lines))
    require(len(designs) == 30, "Fano plane count")
    for design in designs:
        blocks = [set(t) for i, t in enumerate(triples) if design >> i & 1]
        for degree, expected in enumerate((7, 3, 1)):
            for face in combinations(range(7), degree):
                require(sum(set(face) <= b for b in blocks) == expected, "invalid design")
    require(all(any(h & d == 0 for d in designs) for h in patterns), "uncovered seven-site pattern")


def main():
    patterns = maximal_patterns()
    check_upper((0, 1, 2, 4), -1, [0, 1, 0, 1], [0, 1, 0, 0, -1, 0], (-1, 2, 0))
    check_upper((0, 1, 2, 3, 4), 0, [0, -1, -1, -1, 0],
                [1, 1, -1, 0, 2, 2, -1, 2, 1, 1], (0, -3, 8))
    check_upper((0, 2, 3, 4, 6), -1, [1, 0, 1, 0, 1],
                [0, -1, 0, -1, 0, 1, 0, 0, -1, 0], (-1, 3, -2))
    check_upper(tuple(range(6)), -12, [5, 7, 2, 2, 7, 5],
                [0, 5, -5, 0, -5, 3, 3, -10, 0, 3, 3, -5, 3, 5, 0], (-12, 28, 0))
    check_five(patterns[5])
    check_seven(patterns[7])
    print("All four upper inequalities hold on every admissible subset.")
    print("The two five-site distributions cover all 16 maximal ordered patterns.")
    print("The 30 Fano designs cover all 2238 maximal ordered seven-site patterns.")


if __name__ == "__main__":
    main()
