"""Exhaust the EHPS midpoint triples on rational grids by integer arithmetic."""
from dataclasses import dataclass

@dataclass(frozen=True)
class Point:
    a: int
    b: int
    s: int
    potential: int

def block(q, denominator):
    """Coordinates are scaled by q, and the potential is scaled by q squared."""
    points = {}
    for a in range(q):
        for b in range(q):
            s = a + b
            low = 2*a >= q and 2*q < 3*s and 6*s <= 7*q
            high_band = (6*denominator*s >= (7*denominator+6)*q
                         and 12*s <= 17*q)
            high_right = 2*a >= q and 2*b < q
            high_left = (2*a < q and 2*b >= q and
                         2*denominator*(2*a+b) >= (3*denominator+2)*q)
            if not (low or (high_band and (high_right or high_left))):
                continue
            t = a if 2*a < q else a-q//2
            f = 26*denominator**2*s**2 + 6*t**2
            points[a, b] = Point(a, b, s, f)
    return points

def check(q, denominator):
    assert q % 2 == 0
    points = block(q, denominator)
    count = dropped = wrapped = repeated_endpoints = 0
    for x in points.values():
        for y in points.values():
            z = points.get(((2*y.a-x.a) % q, (2*y.b-x.b) % q))
            if z is None:
                continue
            count += 1
            wrapped += int(x.a + z.a != 2*y.a or x.b + z.b != 2*y.b)
            repeated_endpoints += int(x == z and x != y)
            drop = x.s + z.s - 2*y.s
            assert drop in (0, q), (q, x, y, z, drop)
            dropped += int(drop == q)
            lhs = x.potential + z.potential - 2*y.potential
            rhs = ((x.a-z.a)**2 + (x.b-z.b)**2
                   + denominator**2*(x.s-z.s)**2)
            assert lhs >= rhs, (q, x, y, z, lhs, rhs)
    return q, denominator, len(points), count, wrapped, dropped, repeated_endpoints

if __name__ == "__main__":
    print("grid, inverse epsilon, points, ordered triples, wrapped, sum drops, unequal midpoints with equal endpoints")
    for case in [(24, 24), (36, 48), (48, 96), (60, 120), (84, 84)]:
        print(*check(*case), sep=", ")
