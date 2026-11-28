"""Independent finite tests for joint-guard-distribution.md and batch-cap.md.

Uses only the Python standard library. All acceptance tests use integers or
fractions, including the entropy certificates. Run with python joint-guard-check.py.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, product
from math import lcm, prod


def placements(points, rows):
    """Bit masks of all reachable covered subsets after one choice per row."""
    reachable = {0}
    for row in rows:
        groups = defaultdict(int)
        for i, point in enumerate(points):
            groups[row(point)] |= 1 << i
        reachable = {mask | extra for mask in reachable for extra in groups.values()}
    return reachable


@lru_cache(None)
def log_lower(x):
    """Rational lower bound on log x for x>=1 (positive atanh series)."""
    assert x >= 1
    z = (x - 1) / (x + 1)
    return 2 * sum((z**(2*j+1) / (2*j+1) for j in range(12)), Fraction())


def distributions(n, total):
    if n == 1:
        yield (total,)
        return
    for first in range(total+1):
        for rest in distributions(n-1, total-first):
            yield (first, *rest)


def certify_measure(low, qs, owners, guards):
    """Explicitly find a rational witness. This search does not invoke minimax."""
    for weights in sorted(distributions(len(low), 6), key=lambda w: -min(w)):
        money = [Fraction() for q in qs]
        for i, guard in zip(owners, guards):
            bins = Counter()
            for x, w in zip(low, weights):
                bins[guard[x]] += w
            money[i] += Fraction(max(bins.values()), 6 * qs[i])
        entropy = sum(Fraction(w, 6)*log_lower(Fraction(6, w)) for w in weights if w)
        cost = sum(max(0, v-log_lower(Fraction(q))) for q, v in zip(qs, money))
        if cost <= entropy:
            return True
    return False


def check_star_cuts():
    count = Counter()
    patterns = ((0, 0, 0), (0, 1, 0), (0, 0, 1), (0, 1, 2))
    # The complement is any prescribed relation on all three coordinates,
    # including non-product relations. The row pools allow every reassignment.
    for qs, owners in [((2,2), (0,0,1)), ((2,2),(0,0,1,1)), ((2,3),(0,0,1,1))]:
        points = list(product(range(3), *map(range, qs)))
        for seed in range(8):
            guards = tuple(patterns[(seed + i*(1+seed//3)) % len(patterns)]
                           for i in range(len(owners)))
            rows = [(lambda x, i=i, g=g: (g[x[0]], x[1+i])) for i, g in zip(owners, guards)]
            covered = placements(points, rows)
            full = (1 << len(points)) - 1
            maximal = tuple(sorted(covered, key=int.bit_count, reverse=True))
            tested = set()
            for i in range(400):
                # Include the full relation and its slices, then varied sparse holes.
                mask = full if i == 0 else (0x45d9f3b * (i+17) ** 3) & full
                if not mask or mask in tested:
                    continue
                tested.add(mask)
                if any(mask & ~m == 0 for m in maximal):
                    count['coverable relations'] += 1
                    continue
                low = tuple(sorted({x[0] for j,x in enumerate(points) if mask >> j & 1}))
                assert certify_measure(low, qs, owners, guards)
                count['exact rational entropy witnesses'] += 1
    # Many equivalent-looking guards at one owner: full arbitrary placements,
    # one less row than required to cover q*d cells. Entropy witnesses must
    # genuinely spread once the number of rows exceeds q log q.
    for d, q in product(range(2, 7), (2, 3, 5)):
        low = tuple(range(d))
        owners = (0,) * (q*d-1)
        assert certify_measure(low, (q,), owners, (low,)*len(owners))
        count['large repeated-guard tests'] += 1
    return count


def check_batch_product():
    count = Counter()
    for sizes in ((2,2), (2,3), (2,2,2), (2,2,3), (3,3)):
        grid = list(product(*map(range, sizes)))
        for mask in range(1, 1 << len(grid)):
            holes = [y for j,y in enumerate(grid) if mask >> j & 1]
            views = [set(y[i] for y in holes) for i in range(len(sizes))]
            escaped = [sum(all(y[i] != s for i,s in enumerate(target)) for y in holes)
                       for target in product(*views)]
            ways = prod(map(len, views))
            rhs = len(holes)*prod(len(v)-1 for v in views)
            assert sum(escaped) == rhs
            if min(escaped):
                assert ways <= rhs
                count['universally escaping relations'] += 1
                count['equalities'] += (ways == rhs)
            count['exact product enumerations'] += 1
    return count


def largest_prime(n):
    for q in range(n,1,-1):
        if n % q == 0 and all(q % p for p in range(2, int(q**0.5)+1)):
            return q


def coeff_group(n):
    q = largest_prime(n)
    m, j = n, 0
    while m % q == 0:
        m //= q
        j += 1
    return q,j


def check_integers():
    count = Counter()
    for D in [(2,3,4,6,12), (2,3,4,6,8,24), (2,3,4,6,9,18,36),
              (2,3,4,5,6,10,15,20,30)]:
        L = lcm(*D)
        for reserve in D:
            groups = defaultdict(list)
            for n in D:
                if n != reserve:
                    groups[coeff_group(n)].append(n)
            for (q,j), rows in groups.items():
                for batch in combinations(rows,q):
                    # Directly construct the simultaneous CRT classes in integer
                    # coordinates. Enumerate complement union masks without fixing
                    # any remaining residue to the original covering witness.
                    g = lcm(*(n//q for n in batch))
                    for target in range(g):
                        residues = [next(r for r in range(n) if r % (n//q) == target % (n//q)
                                         and r//q**(j-1) % q == i) for i,n in enumerate(batch)]
                        assert all(any(x % n == r for n,r in zip(batch,residues))
                                   for x in range(target,L,g))
                        count['integer batch placements'] += 1
                    old = [n for n in D if n != reserve and n not in batch]
                    masks = placements(range(L), [lambda x,n=n: x % n for n in old])
                    for mask in masks:
                        b = len({x % g for x in range(L) if not mask >> x & 1})
                        assert b >= 2
                        count['integer complementary masks'] += 1
    return count


def pair_reserves():
    # Reserve a ceiling-rounded quota at exactly this pair. After endpoint
    # slots are assigned, require a separate multiplicative cofactor gap.
    count = Counter()
    pairs = tuple(product((3, 5, 7), (11, 13, 17)))
    for seed, factor in product(range(80), (1, 2, 3)):
        groups = {pair: [] for pair in pairs}
        for p,q in pairs:
            # Unique large-prime pair, with all dressings 2-smooth.
            groups[p,q] = [2**j for j in range(20) if (j+1)*(p+seed+1)%17 != q%17]
        prefix, slots, remaining = {}, defaultdict(list), []
        for (p,q), ds in groups.items():
            size = (q*factor+p-1)//p
            prefix[p,q] = ds[:size]
            remaining.extend((p*q*d,p,q,d) for d in ds[size:])
        occupied = {p*q*d for (p,q), ds in prefix.items() for d in ds}
        rejects = []
        for n,p,q,d in sorted(remaining):
            v = next((v for v in (p,q) if len(slots[v]) < v//3), None)
            if v is None:
                if d > 4*max(prefix[p,q]):
                    rejects.append((p,q,d))
            else:
                assert n not in occupied
                occupied.add(n)
                slots[v].append(n)
        for p,q,d in rejects:
            assert len(prefix[p,q])*p >= q*factor
            assert all(4*dp < d for dp in prefix[p,q])
            assert all(len(slots[v]) == v//3 and max(slots[v]) < p*q*d for v in (p,q))
        count['reserve and gap instances'] += 1
        count['retained pair-row incidences'] += len(rejects)
    return count


def stage_examples():
    count = Counter()
    for z in (11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71):
        L = lcm(*range(1,z))
        rows = []
        for p in range(2,z):
            if largest_prime(p) != p:
                continue
            power = p
            while L % power == 0:
                rows.extend(power*d for d in range(1,p))
                power *= p
        extra = 6*(z//6+1)
        tail = [z*d for d in (*range(1,z),extra)]
        D = rows+tail
        assert len(D) == len(set(D)) and lcm(*D) == z*L and max(D) == z*extra
        assert lcm(*(n//z for n in tail)) == L
        assert all(t == q-1 for (q,j),t in Counter(map(coeff_group,D[:-1])).items())
        count['prime-stage examples'] += 1
        if z == 11:
            # Directly verify all integer residues over period 27720.
            classes = []
            seen = Counter()
            for n in rows:
                q,j = coeff_group(n)
                seen[q,j] += 1
                r = next(a for a in range(n) if a % (n//q) == 0 and a//q**(j-1) % q == seen[q,j])
                classes.append((n,r))
            for i,n in enumerate(tail):
                r = next(a for a in range(n) if a % (n//z) == 0 and a % z == i)
                classes.append((n,r))
            assert all(any(x % n == r for n,r in classes) for x in range(z*L))
            count['residues checked in prime-stage witness'] = z*L
    return count


if __name__ == '__main__':
    for check in (check_star_cuts, check_batch_product, check_integers, pair_reserves, stage_examples):
        print(check.__name__, dict(check()), flush=True)
