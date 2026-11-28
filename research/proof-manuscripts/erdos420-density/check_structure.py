"""Exact checks for the residue change of variables and suffix selection in the #420 proof."""
from itertools import combinations
from math import gcd, prod


def residue_change():
    h = (3, 5, 11)
    checked_pairs = checked_progressions = 0
    for D in range(1, 6):
        special = {D * s for s in h}
        for W in (6, 30, 42):
            for b in range(W):
                if any(gcd(b + a, W) > 1 for a in h):
                    continue
                for j in range(1, 41):
                    if j in special:
                        continue
                    for r in range(1, 26):
                        g = gcd(D * W, r)
                        modulus = r // g
                        initial = D * b + j
                        direct = [n for n in range(modulus) if (D*W*n + initial) % r == 0]
                        if initial % g:
                            assert not direct
                            continue
                        u = (-(initial // g) * pow(D * W // g, -1, modulus)) % modulus
                        assert direct == [u]
                        forms = [(W*modulus, W*u+b+s) for s in h]
                        forms.append((D*W//g, (D*(W*u+b)+j)//r))
                        for v in (-3, 0, 2):
                            original_t = b + W*(u+modulus*v)
                            assert all(a*v+c == original_t+s for (a,c), s in zip(forms, h))
                            assert r*(forms[-1][0]*v+forms[-1][1]) == D*original_t+j
                        disc = prod(a for a, _ in forms)
                        for (a, c), (a1, c1) in combinations(forms, 2):
                            disc *= a*c1-a1*c
                        assert disc
                        checked_progressions += 1
                        for p in (5, 7, 11, 13, 17, 19):
                            if disc % p:
                                roots = {(-c*pow(a, -1, p)) % p for a,c in forms}
                                assert len(roots) == len(forms)
                                checked_pairs += 1
    return checked_progressions, checked_pairs


def suffix_selection():
    tests = 0
    positions = (1, 4, 9, 15, 30, 45, 67, 82, 100, 144)
    for mask in range(1, 1 << len(positions)):
        selected = [h for i, h in enumerate(positions) if mask >> i & 1]
        for r in range(1, len(selected)+1):
            n = selected[-r]-1
            for length in (positions[-1], positions[-1]+1, 5*positions[-1]):
                assert sum(n < h <= n+length for h in selected) == r
                tests += 1
    return tests


if __name__ == '__main__':
    a,b = residue_change()
    print(a, 'soluble congruences checked, counting solutions and lifting all forms.')
    print(b, 'good-prime root counts checked.')
    print(suffix_selection(), 'suffix lengths checked for every nonempty pattern on ten sites.')
