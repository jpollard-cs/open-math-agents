"""Independent full-period checks for both repaired assignments and the packing dual."""
from collections import Counter
from math import isqrt
import json
from pathlib import Path


def read(name):
    return json.loads(Path(__file__).with_name(name).read_text())


def divisors(n):
    small = [d for d in range(1, isqrt(n) + 1) if n % d == 0]
    return sorted(set(small + [n // d for d in small]))


def uncovered(period, rows):
    assert len(set(d for d, _ in rows)) == len(rows)
    covered = bytearray(period)
    for d, a in rows:
        assert d > 1 and period % d == 0 and 0 <= a < d
        covered[a::d] = bytes([1]) * (period // d)
    return [i for i, value in enumerate(covered) if not value]


def main():
    base = read("candidate773500.json")
    n = base["period"]
    old = base["modulus_residue"]
    holes = uncovered(n, old)
    assert n == 773500 and holes == sorted(base["uncovered"])
    assert len(old) == 95 and len(holes) == 8
    for prime, count, filename in [(5, 12, "lift3867500.json"), (13, 42, "lift13.json")]:
        data = read(filename)
        new = data["additional_modulus_residue"]
        assert (data["lower_period"], data["period"]) == (n, n * prime)
        assert len(new) == count and all(n % d for d, _ in new)
        assert uncovered(n * prime, old + new) == []
        print(n * prime, "fully covered with", len(new), "new moduli")

    for q, counts in [(125, [2, 6]), (13, [1, 2, 5]), (17, [1, 1, 1, 2, 3])]:
        assert sorted(Counter(x % q for x in holes).values()) == counts
    ds = divisors(n)
    assert len(ds) == 96
    marked = [holes[i] for i in (0, 2, 5, 6, 7)]
    dual = sum(max(Counter(x % d for x in marked).values()) for d in ds)
    groups = read("guard-copies.json")
    used = []
    for group in groups:
        for d, a in group:
            assert n % d == 0 and 0 <= a < d
            used.append(d)
        assert all(any(x % d == a for d, a in group) for x in holes)
    assert len(used) == len(set(used))
    assert len(groups) == dual // len(marked) == 34 and dual == 174
    print("guard packing", len(groups), "dual numerator", dual)


if __name__ == "__main__":
    main()
