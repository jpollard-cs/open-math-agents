"""Independent 3-by-5 board enumeration and a 61-row integer certificate."""
from functools import lru_cache
from itertools import combinations_with_replacement, permutations, product
from math import prod


def permuted(mask, perm):
    return sum(((mask >> i) & 1) << perm[i] for i in range(3))


def optimize():
    perms = list(permutations(range(3)))
    best = 999
    smallest_holes = 999
    witness = None
    checked = 0
    # Each column records its three forbidden bits. Sorting quotients only
    # coordinate permutations, without any monotone compression.
    for cols in combinations_with_replacement(range(8), 5):
        x=sum(m.bit_count() for m in cols)
        if x>8:
            continue
        if any(tuple(sorted(permuted(m,p) for m in cols)) < cols for p in perms):
            continue
        checked+=1
        options={}
        for first,second in product(range(8),range(32)):
            counts=(first.bit_count(),second.bit_count())
            holes=sum((7 & ~(first|m)).bit_count() for j,m in enumerate(cols)
                      if not second>>j & 1)
            current = options.get(counts)
            if current is None or holes < current[0]:
                options[counts]=(holes,first,second)
        @lru_cache(None)
        def dp(layers,y,z):
            if layers==0: return 0
            return min(h+dp(layers-1,y-i,z-j) for (i,j),(h,_,_) in options.items()
                       if i<=y and j<=z)
        for y,z in product(range(9),repeat=2):
            h=dp(9,y,z)
            smallest_holes=min(smallest_holes,h)
            if h<=8 and x+y+z+h < best:
                best=x+y+z+h
                slices=[]
                yy,zz=y,z
                for layers in range(9,0,-1):
                    for (i,j),(g,first,second) in options.items():
                        if i<=yy and j<=zz and g+dp(layers-1,yy-i,zz-j)==dp(layers,yy,zz):
                            slices.append((first,second))
                            yy-=i
                            zz-=j
                            break
                witness=(cols,slices,h,x,y,z)
        dp.cache_clear()
    assert best==30 and smallest_holes==6
    print(checked, 'labelled-board orbits; minimum pair-plus-triple count',best,
          'least number of holes at maximal budgets',smallest_holes)
    return witness


def make_rows(witness):
    cols,slices,h,x,y,z=witness
    ds=(1,2,3,5,6,10,15,30)
    # Ordinary guards leave precisely zero in the old coordinates.
    rows=[(2,1),(3,2),(6,4)]+[(n,(6*j)%n) for j,n in enumerate((5,10,15,30),1)]
    groups={}
    for r in (11,13,17):
        groups[r]=list(range(1,9))
    def label(p,i):
        return 0 if i==0 else 8+i
    def put(coords):
        m=prod(r for r,i in coords)
        residue=next(t for t in range(m) if all(t%r==label(r,i) for r,i in coords))
        groups.setdefault(m,[]).append(residue)
    for j,mask in enumerate(cols):
        for i in range(3):
            if mask>>i&1: put(((11,i),(13,j)))
    for k,(first,second) in enumerate(slices):
        for i in range(3):
            if first>>i&1: put(((11,i),(17,k)))
        for j in range(5):
            if second>>j&1: put(((13,j),(17,k)))
        for i,j in product(range(3),range(5)):
            if not ((cols[j]|first)>>i&1 or second>>j&1):
                put(((11,i),(13,j),(17,k)))
    for support,phases in groups.items():
        guards=(30,1,2,3,5,6,10,15) if support==2431 else ds
        for d,a in zip(guards,phases,strict=False):
            rows.append((d*support,d*((a*pow(d,-1,support))%support)))
        assert len(phases)<=len(ds)
    assert len(rows)==len(dict(rows))==61 and max(dict(rows))==72930
    hits=bytearray(72930)
    for n,a in rows: hits[a::n]=bytes([1])*(72930//n)
    assert all(hits)
    return sorted(rows)


if __name__=='__main__':
    w=optimize()
    print('dimensions/budgets',w[-3:],'witness holes',w[2])
    print(make_rows(w))
