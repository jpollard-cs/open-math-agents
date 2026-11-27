"""Enumerate irreducible sets up to a modulus cap by prime-power contraction."""
import argparse
import json
from functools import cache, lru_cache
from itertools import combinations
from math import lcm
from pathlib import Path

@cache
def prime_powers(n):
    result = []
    p = 2
    while p * p <= n:
        power = 1
        while n % p == 0:
            n //= p
            power *= p
        if power > 1:
            result.append((p, power))
        p += 1
    if n > 1:
        result.append((n, n))
    return tuple(result)

def modulus_pool(cap):
    period = 1
    for p in range(2, cap + 1):
        if prime_powers(p) != ((p, p),):
            continue
        power = p
        while (p + 1) * power <= cap:
            period *= p
            power *= p
    return [n for n in range(2, cap + 1) if period % n == 0]

@cache
def row_masks(period, n):
    residue_zero = ((1 << period) - 1) // ((1 << n) - 1)
    return tuple(residue_zero << a for a in range(n))

@cache
def can_cover(moduli):
    if 1 in moduli:
        return True
    period = lcm(*moduli)
    if sum(period // n for n in moduli) < period:
        return False

    reductions = []
    for p, power in prime_powers(period):
        top = [n for n in moduli if n % power == 0]
        reductions.append((len(top) - p, p, power, top))
    if not reductions:
        return False
    excess, p, power, top = min(reductions)
    if excess <= 0:
        other = [n for n in moduli if n % power]
        if excess == 0:
            other.append(lcm(*(n // p for n in top)))
        return can_cover(tuple(sorted(other)))

    rows = [row_masks(period, n) for n in moduli]
    @lru_cache(maxsize=5000)
    def search(i, holes):
        if holes == 0:
            return True
        if i == len(rows):
            return False
        gains = [{holes & mask for mask in row} for row in rows[i:]]
        best = [max(map(int.bit_count, row)) for row in gains]
        need = holes.bit_count() - sum(best[1:])
        if need > best[0]:
            return False
        for covered in sorted(gains[0], key=int.bit_count, reverse=True):
            if covered and covered.bit_count() >= need and search(i + 1, holes ^ covered):
                return True
        # A zero-gain option is dominated by every positive-gain option.
        return False
    return search(1, ((1 << period) - 1) ^ rows[0][0])

def enumerate_sets(cap):
    pool = modulus_pool(cap)
    minimal, found_bits = [], []
    for k in range(1, len(pool) + 1):
        for indices in combinations(range(len(pool)), k):
            moduli = tuple(pool[i] for i in indices)
            period = lcm(*moduli)
            if sum(period // n for n in moduli) < period:
                continue
            if any(sum(n % power == 0 for n in moduli) < p
                   for p,power in prime_powers(period)):
                continue
            bits = sum(1 << i for i in indices)
            if any(bits & earlier == earlier for earlier in found_bits):
                continue
            if can_cover(moduli):
                minimal.append(moduli)
                found_bits.append(bits)
    return minimal

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('cap', type=int, default=47, nargs='?')
    cap = parser.parse_args().cap
    result = enumerate_sets(cap)
    output = Path(f'covers-through-{cap}.json')
    output.write_text(json.dumps(result) + '\n')
    print(f'{len(result)} irreducible sets, written to {output}')
    for k in sorted(set(map(len,result))):
        print(k, min(s[-1] for s in result if len(s) == k))
