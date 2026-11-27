"""Test an irreducible arithmetic packet and independent finite fibre enumeration."""
from itertools import product
from math import lcm
from pathlib import Path
import argparse,json

def crt(a,m,b,n):
    return (a + m*((b-a)*pow(m,-1,n) % n)) % (m*n)

def build():
    left=(3,5)
    right=(7,11,13,17)
    dress=(32,64)
    ordinary={2**j:2**(j-1) for j in range(1,13)}
    raw=[]
    for p in left:
        for i in range(p-2):
            raw.append((p,2+i,2**i))
    for q,v in zip(right, product(range(2), repeat=2)):
        for i in range(q-4):
            raw.append((q,4+i,2**i))
        for i,p in enumerate(left):
            for j,d in enumerate(dress):
                raw.append((p*q,crt(v[i],p,2*i+j,q),d))
    assert lcm(*(d for _,_,d in raw))==4096
    rows=ordinary.copy()
    for n,a,d in raw:
        assert d*n not in rows
        rows[d*n]=crt(0,d,a,n)
    # Binary side rows cover every residue other than the distinguished class.
    holes=[x for x in range(4096) if not any(x%n==a for n,a in ordinary.items())]
    assert holes==[0]
    # Above 0 modulo 4096 each dressed class is active exactly on its raw residue.
    Q=lcm(*(n for n,_,_ in raw))
    hits=bytearray(Q)
    for n,a,d in raw:
        assert rows[d*n]%d==0 and rows[d*n]%n==a
        hits[a::n]=bytes([1])*(Q//n)
    assert all(hits)
    assert all(p*q*b in rows for p in left for q in right for b in dress)
    print(f'{len(rows)} distinct moduli, maximum {max(rows)}, period {4096*Q}; '
          f'{len(raw)} raw indices, all {Q} internal residues covered.')
    return rows

def masks(left_sizes,right_size,neighbor_counts):
    # Freely choose left and right residue on each indexed pair, then test all fibres.
    # Labels outside the residual domains can only shrink the killed set.
    coords=[i for i,n in enumerate(neighbor_counts) for _ in range(n)]
    domain=list(product(*(range(b) for b in left_sizes)))
    options=[list(product(range(left_sizes[i]),range(right_size))) for i in coords]
    out=set()
    for assn in product(*options):
        killed=0
        for j,x in enumerate(domain):
            colors={r for i,(a,r) in zip(coords,assn) if x[i]==a}
            if len(colors)==right_size:
                killed |= 1<<j
        out.add(killed)
    return out

def crosscheck():
    tests=[((2,2),4,(2,2)),((2,2),4,(1,2)),((2,2),4,(2,1)),
           ((2,2),5,(2,2)),((3,2),4,(2,2)),((2,3),4,(2,2))]
    checked=0
    for domain,b,counts in tests:
        actual=masks(domain,b,counts)
        count=domain[0]*domain[1]
        expected={0}|({1<<i for i in range(count)} if sum(counts)==b else set())
        assert actual==expected
        unions={0}
        for _ in range(4):
            unions={a|c for a in unions for c in actual}
        assert ((1<<count)-1 in unions)==(sum(counts)==b and count<=4)
        checked+=(domain[0]*b)**counts[0]*(domain[1]*b)**counts[1]
    print(f'{checked} unrestricted assignments on the residual coordinates checked across six cases.')

if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--export',type=Path)
    args=ap.parse_args()
    rows=build()
    crosscheck()
    if args.export:
        args.export.write_text(json.dumps(sorted(rows.items()))+'\n')
