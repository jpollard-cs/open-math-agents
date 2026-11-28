"""Independent finite certificates for the two exceptional seeds in the theorem."""
from math import gcd, lcm

SEEDS = {
    3: (2,3,8,9,12,16,18,24,36,48),
    5: (2,3,5,8,10,12,15,20,24,30,40),
}


def choose_residues(moduli):
    """Give one covering tuple. Translate by earlier lcms to break symmetry."""
    N = lcm(*moduli)
    jobs = []
    earlier = 1
    for m in moduli:
        masks = [sum(1 << x for x in range(r,N,m)) for r in range(gcd(earlier,m))]
        jobs.append(masks)
        earlier = lcm(earlier,m)
    def visit(idx,uncovered):
        if idx == len(jobs):
            return () if uncovered == 0 else None
        if sum(max((h & uncovered).bit_count() for h in group) for group in jobs[idx:]) < uncovered.bit_count():
            return None
        for r,mask in sorted(enumerate(jobs[idx]), key=lambda z: -(z[1] & uncovered).bit_count()):
            suffix = visit(idx+1,uncovered & ~mask)
            if suffix is not None:
                return (r,)+suffix
        return None
    return visit(0,(1 << N)-1)


def largest_row_minimum(moduli, period):
    """Maximize the least capacity of an odd residue row, in binary sites."""
    H = period & -period
    q = period//H
    row_sums = [0]*q
    jobs = []
    earlier = 1
    for m in moduli:
        binary = m & -m
        t = m//binary
        jobs.append((t,H//binary,gcd(t,earlier)))
        earlier = lcm(t,earlier)
    def visit(i):
        if i == len(jobs):
            return min(row_sums)
        t,w,limit = jobs[i]
        best = 0
        for r in range(limit):
            for x in range(r,q,t): row_sums[x] += w
            best = max(best,visit(i+1))
            for x in range(r,q,t): row_sums[x] -= w
        return best
    return visit(0)


if __name__ == '__main__':
    for p,S in SEEDS.items():
        N = lcm(*S)
        residues = choose_residues(S)
        assert residues is not None
        assert all(any(x%m==r for m,r in zip(S,residues)) for x in range(N))
        maxima=[largest_row_minimum(S[:j]+S[j+1:],N) for j in range(len(S))]
        assert max(maxima) < (N & -N)
        print('odd part',p,'period',N,'moduli',S,'\nresidues',residues,'\nrow maxima',maxima,flush=True)
