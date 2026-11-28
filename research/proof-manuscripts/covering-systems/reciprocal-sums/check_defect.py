"""Check the finite defect bound using exact rational arithmetic."""
from fractions import Fraction
from functools import cache
from math import lcm
import json
from pathlib import Path

@cache
def parameters(period):
    residual = period
    slots = 0
    ideal = set()
    p = 2
    while residual > 1:
        power = 1
        while residual % p == 0:
            residual //= p
            power *= p
            slots += p - 1
            for d in range(1,p):
                assert d*power not in ideal
                ideal.add(d*power)
        p += 1
    return slots, ideal, sum(Fraction(1,n) for n in ideal)

def verify(moduli):
    period = lcm(*moduli)
    largest = max(moduli)
    slots, ideal, mass = parameters(period)
    defect = len(moduli) - 1 - slots
    assert defect >= 0
    total = sum(Fraction(1,n) for n in moduli)
    exceptions = [n for n in range(2,largest+2) if period % n == 0 and n not in ideal]
    all_exceptions = [n for n in range(2,period+1) if period % n == 0 and n not in ideal]
    discrete_bound = Fraction(1,largest) + mass + sum(Fraction(1,n) for n in all_exceptions[:defect])
    assert total <= discrete_bound, (moduli, total, discrete_bound)
    for y in range(1,largest+2):
        change = sum(Fraction(1,n) - Fraction(1,y) for n in exceptions if n <= y)
        bound = Fraction(1,largest) + mass + Fraction(defect,y) + change
        assert total <= bound, (moduli, y, total, bound)
    return largest+1

if __name__ == '__main__':
    data = json.loads(Path(__file__).with_name('covers-through-47.json').read_text())
    tests = sum(verify(row) for row in data)
    print(f'{tests:,} rational inequalities verified across {len(data):,} covers.')
