"""Independent finite enumeration for the component theorem. Only the Python standard library."""
from collections import Counter
from functools import cache
from itertools import combinations, product
from math import prod


@cache
def all_classes(sizes, support):
    points = tuple(product(*(range(p) for p in sizes)))
    indices = tuple(i for i in range(len(sizes)) if support & (1 << i))
    result = {}
    for j, point in enumerate(points):
        key = tuple(point[i] for i in indices)
        result[key] = result.get(key, 0) | (1 << j)
    return result


@cache
def attainable(sizes, shapes):
    if not shapes:
        return frozenset([0])
    choices = all_classes(sizes, shapes[-1]).values()
    return frozenset(mask | new for mask in attainable(sizes, shapes[:-1]) for new in choices)


@cache
def minimum(sizes, shapes):
    return prod(sizes) - max(x.bit_count() for x in attainable(sizes, shapes))


@cache
def indispensable(sizes, shapes):
    return minimum(sizes, shapes) == 1 and all(
        minimum(sizes, shapes[:i] + shapes[i+1:]) >= 2
        for i in range(len(shapes)) if i == 0 or shapes[i-1] != shapes[i])


def components(dim, rows):
    closure = [1 << i for i in range(dim)]
    for shape, changed, _ in rows:
        for i in range(dim):
            if changed & (1 << i):
                closure[i] |= shape
    for j in range(dim):
        for i in range(dim):
            if closure[i] & (1 << j):
                closure[i] |= closure[j]
    return sorted({sum(1 << j for j in range(dim)
                       if closure[i] & (1 << j) and closure[j] & (1 << i))
                   for i in range(dim)})


def classify(sizes, limit):
    dim = len(sizes)
    full = 2**dim - 1
    usable = []
    for shape in range(1, full+1):
        indices = [i for i in range(dim) if shape & (1 << i)]
        for assignment, mask in all_classes(sizes, shape).items():
            changed = sum(1 << i for i, a in zip(indices, assignment) if a != 0)
            if changed:
                usable.append((shape, changed, mask))
    target = (1 << prod(sizes)) - 2
    stats = Counter()
    for count in range(1, limit+1):
        for rows in combinations(usable, count):
            mask = 0
            for _, _, used in rows:
                mask |= used
            if mask != target:
                continue
            stats["unique_zero_assignments"] += 1
            shapes = tuple(sorted(shape for shape, _, _ in rows))
            actual = indispensable(sizes, shapes)
            local = True
            parts = components(dim, rows)
            for part in parts:
                indices = [i for i in range(dim) if part & (1 << i)]
                section = [sum(1 << j for j,i in enumerate(indices) if shape & (1 << i))
                           for shape, changed, _ in rows if changed & part]
                local_sizes = tuple(sizes[i] for i in indices)
                local_shapes = tuple(sorted(section))
                local &= indispensable(local_sizes, local_shapes)
                if actual:
                    for support, multiple in Counter(local_shapes).items():
                        assert multiple < prod(s for j,s in enumerate(local_sizes) if support & (1 << j))
            assert actual == local, (sizes, rows)
            if actual:
                stats["irreducible_assignments"] += 1
                stats["multiple_components"] += int(len(parts) > 1)
                stats["irreducible_shapes_and_deletions_tested"] += 1 + count
    return stats


if __name__ == "__main__":
    total = Counter()
    for grid, bound in [((2, 2), 4), ((2, 3), 5), ((2, 2, 2), 6)]:
        result = classify(grid, bound)
        print(grid, bound, dict(result))
        total += result
    print("combined", dict(total))
