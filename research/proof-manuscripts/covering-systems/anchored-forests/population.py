"""Exact complement density of a finite union of sets of multiples."""
from fractions import Fraction
from functools import cache
from math import gcd
from pathlib import Path
import json


def read_table():
    return json.loads(Path(__file__).with_name("table2-confirmed.json").read_text())


def reduce_set(numbers):
    minimal = []
    for n in sorted(set(numbers)):
        if all(n % d for d in minimal):
            minimal.append(n)
    return tuple(minimal)


def smallest_prime(n):
    p = 2
    while p * p <= n:
        if n % p == 0:
            return p
        p += 1
    return n


def valuation(n, p):
    exponent = 0
    while n % p == 0:
        exponent += 1
        n //= p
    return exponent


@cache
def uncovered(numbers):
    if not numbers:
        return Fraction(1)
    if numbers[0] == 1:
        return Fraction(0)
    p = min(map(smallest_prime, numbers))
    largest_exponent = max(valuation(n, p) for n in numbers)
    total = Fraction(0)
    for e in range(largest_exponent + 1):
        quotients = (n // gcd(n, p**e) for n in numbers)
        remaining = reduce_set(q for q in quotients if q % p)
        if e == largest_exponent:
            probability = Fraction(1, p**e)
        else:
            probability = Fraction(p - 1, p**(e + 1))
        total += probability * uncovered(remaining)
    return total
