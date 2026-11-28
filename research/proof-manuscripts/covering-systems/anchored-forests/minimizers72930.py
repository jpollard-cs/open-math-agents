"""Classify all 61-element minimizers by the two omitted fresh supports."""
from collections import Counter
from itertools import combinations_with_replacement
from math import comb
from triple_fibres import least_holes

def check():
    counts = Counter()
    tot = 0
    for pair in combinations_with_replacement(range(7), 2):
        budgets = [8 - pair.count(j) for j in range(7)]
        widths = [prime - budget for prime, budget in zip((11,13,17), budgets)]
        h = least_holes(*widths, *budgets[3:6])
        if h <= budgets[6]:
            counts[pair] = comb(8,2) if pair[0] == pair[1] else 64
            tot += counts[pair]
    print('Support order is p, q, r, pq, pr, qr, pqr.')
    for pair, number in counts.items(): print(pair, number)
    print('Total number of distinct minimum sets:', tot)
    assert dict(counts) == {(6, 6): 28} and tot == 28
    return counts, tot

if __name__ == '__main__':
    check()
