"""Check explicit covers and compare the decision with a direct integer program."""
import argparse
from ast import literal_eval
from pathlib import Path

from spectrum import fixed_size, prime_factors, zero_defect_cover


def required_count(period):
    return 1 + sum(p - 1 for p in prime_factors(period))


def direct_decision(period):
    """Fix the essential singleton at zero, then choose proper divisors and residues."""
    import numpy as np
    from scipy.optimize import Bounds, LinearConstraint, milp
    from scipy.sparse import coo_matrix

    divisors = [m for m in range(2, period) if period % m == 0]
    needed = required_count(period) - 1
    if len(divisors) < needed:
        return False
    # Each variable represents one congruence, with nonzero residue to miss zero.
    # At most one per divisor, exactly 'needed' in all, and every nonzero site hit.
    row_indices = []
    column_indices = []
    column = 0
    for i, modulus in enumerate(divisors):
        for residue in range(1, modulus):
            rows = [0, 1 + i] + [
                len(divisors) + x for x in range(residue, period, modulus)
            ]
            row_indices.extend(rows)
            column_indices.extend([column] * len(rows))
            column += 1
    matrix = coo_matrix((np.ones(len(row_indices)), (row_indices, column_indices)),
                        shape=(period + len(divisors), column)).tocsc()
    low = [needed] + [0] * len(divisors) + [1] * (period - 1)
    high = [needed] + [1] * len(divisors) + [np.inf] * (period - 1)
    result = milp(np.zeros(column), integrality=np.ones(column), bounds=Bounds(0, 1),
                  constraints=LinearConstraint(matrix, low, high))
    if result.status not in (0, 2):
        raise RuntimeError(result.message)
    if result.status == 0:
        load = matrix @ np.rint(result.x)
        assert np.all(load >= low) and np.all(load <= high)
    return result.status == 0


def check(limit, direct_limit, data):
    positive = 0
    for m in range(2, limit + 1):
        cover = zero_defect_cover(m)
        k = required_count(m)
        assert (fixed_size(k, m)[0] == 'attainable') == (cover is not None)
        if m <= direct_limit:
            assert direct_decision(m) == (cover is not None), m
        if cover is None:
            continue
        assert len(cover) == k and max(cover) == m and cover[m] == 0
        hits = bytearray(m)
        for d, r in cover.items():
            assert m % d == 0 and 0 <= r < d
            hits[r::d] = bytes([1]) * (m // d)
        assert all(hits)
        positive += 1
    print(f'All {positive} constructed witnesses through {limit} cover their full period.')
    print(f'Direct feasibility agrees for every period from 2 through {direct_limit}.')
    if data:
        observed = set()
        for line in Path(data).read_text().splitlines():
            if not line.startswith('['):
                continue
            row = list(literal_eval(line.split(']')[0] + ']'))
            while len(row) <= 10:
                if len(row) == required_count(max(row)):
                    observed.add((len(row), max(row)))
                row = [2] + [2*d for d in row]
        predicted = {(required_count(m), m) for m in range(2, 513)
                     if required_count(m) <= 10 and zero_defect_cover(m) is not None}
        assert predicted == observed, predicted ^ observed
        print(f'The published list through size ten gives the same {len(observed)} size/maximum pairs.')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--limit', type=int, default=10000)
    parser.add_argument('--direct-limit', type=int, default=240)
    parser.add_argument('--data', help='Agrawal et al. GoodModuliLists_UpTo10Moduli.txt')
    opts = parser.parse_args()
    check(opts.limit, opts.direct_limit, opts.data)
