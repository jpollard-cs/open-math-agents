"""Least uncovered cells of a box with three budgets of axis-parallel lines."""
from functools import lru_cache
from itertools import combinations, product


def partitions(area, rows, cols):
    """Row lengths of all Ferrers boards of the specified area."""
    if not rows:
        if not area:
            yield ()
        return
    for first in range(min(area, cols), (area + rows - 1) // rows - 1, -1):
        for tail in partitions(area - first, rows - 1, first):
            yield (first,) + tail


def least_holes(a, b, c, ab, ac, bc):
    """Exact integer minimum over all placements. A line fixes its named pair."""
    if min(a, b, c) < 1 or min(ab, ac, bc) < 0:
        raise ValueError("positive dimensions and nonnegative budgets required")
    if ab >= a*b or ac >= a*c or bc >= b*c:
        return 0
    best = a*b*c
    for shape in partitions(ab, a, b):
        costs = [(u, v, sum(max(0, b-v-w) for w in shape[:a-u]))
                 for u in range(min(a, ac)+1) for v in range(min(b, bc)+1)]
        @lru_cache(None)
        def suffix(n, x, y):
            if n == 0:
                return 0
            return min(cost + suffix(n-1, x-u, y-v)
                       for u, v, cost in costs if u <= x and v <= y)
        best = min(best, suffix(c, ac, bc))
        suffix.cache_clear()
        if best == 0:
            break
    return best


def line_masks(a, b, c):
    out = []
    points = list(product(range(a), range(b), range(c)))
    for i, j in ((0,1),(0,2),(1,2)):
        pairs = sorted({(x[i], x[j]) for x in points})
        out.append([sum(1 << k for k,x in enumerate(points) if (x[i],x[j]) == pair)
                    for pair in pairs])
    return out


def mask_table(a, b, c):
    """Independent exhaustive union of actual labelled lines."""
    choices = []
    for lines in line_masks(a,b,c):
        choices.append([[sum(sel) for sel in combinations(lines,n)]
                        for n in range(len(lines)+1)])
    answer = {}
    for i,j,k in product(*(range(len(x)) for x in choices)):
        answer[i,j,k] = a*b*c - max((x|y|z).bit_count() for x,y,z in product(
            choices[0][i], choices[1][j], choices[2][k]))
    return answer


def check():
    nchecks = 0
    for box in ((1,2,3),(2,2,2),(2,2,3),(2,3,3)):
        table = mask_table(*box)
        for counts, exact in table.items():
            assert least_holes(*box, *counts) == exact, (box,counts)
            nchecks += 1
    print(nchecks, "integral minima agree with exhaustive line unions")


if __name__ == "__main__":
    check()
