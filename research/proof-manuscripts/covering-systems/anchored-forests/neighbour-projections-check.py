"""Direct actual-residue checks of thinning a prime position before projecting old holes."""
from fractions import Fraction
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
from runpy import run_path

companion = run_path(str(Path(__file__).with_name("projected-holes-check.py")))
divisors = companion["divisors"]
harmonic = companion["harmonic"]
example = run_path(str(Path(__file__).with_name("prime-position-sieve-check.py")))["example"]


def check():
    rows = example()
    count = 0
    # At p=7 this includes all 2^7 subsets before reserving a row, and every
    # deletion pattern after reserving a seven-row modulus.
    p = 7
    K = 60
    for reserve, _ in rows:
        old = [(n, r) for n, r in rows if n != reserve and K % n == 0]
        available = [n // p for n, _ in rows if n != reserve and n % p == 0]
        for assign_zero in (False, True):
            holes = [x for x in range(K) if all(x % n != (0 if assign_zero else r)
                                                 for n, r in old)]
            for size in range(len(available) + 1):
                for cs in combinations(available, size):
                    C = lcm(*cs)
                    qs = [q for q in divisors(C) if len(divisors(q)) == 2]
                    for g in divisors(C):
                        b = len({x % g for x in holes})
                        groups = {c // gcd(c, g) for c in cs}
                        for v in groups:
                            members = [c for c in cs if c // gcd(c, g) == v]
                            assert (g * v) in divisors(C)
                            traces = {tuple(x % c for c in members) for x in holes}
                            assert len(members) < p * len(traces) <= p * b * v
                        count += 1
                    for cut in range(len(qs) + 1):
                        for E in combinations(qs, cut):
                            removed = [c for c in cs if any(c % q == 0 for q in E)]
                            charge = sum(Fraction(1, c) for c in removed)
                            assert charge <= harmonic(len(cs)) * sum(Fraction(1, q) for q in E)
    return count


if __name__ == "__main__":
    print("subcollection and projection tests:", check())
