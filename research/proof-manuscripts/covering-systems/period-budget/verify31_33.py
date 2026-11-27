"""Replay the finite search certificates for the minima at sizes 31, 32 and 33."""
import argparse
import json
from collections import Counter
from itertools import combinations
from math import lcm
from pathlib import Path
from decide96 import decide

def read(name):
    return json.loads(Path(name).read_text())

def covers_at_older_caps(pool, cap60_file):
    position = {n: 1 << i for i,n in enumerate(pool)}
    def bits(row):
        return sum(position[n] for n in row)
    known = {bits(row) for row in read(cap60_file)}
    for name in ('example26.json','extremizers27.json','examples28_84.json','size29-yes.json'):
        known.update(bits(row) for row in read(name))
    for name in ('witness28-second.jsonl','witness30.jsonl'):
        known.add(bits(n for n,_ in read(name)))
    earlier = read('cap84-final-audit.json')
    pool84 = set(earlier['pool_through_84'])
    for omitted, removable, minimal in earlier['rows']:
        if removable or minimal:
            row = pool84 - set(omitted)
            if removable:
                row.remove(removable)
            known.add(bits(row))
    return bits, sorted(known,key=int.bit_count)

def initial31(pool, catalog):
    bits, known = covers_at_older_caps(pool, catalog)
    free = sorted(set(pool)-{32,48,96})
    cases = set()
    for omitted in combinations(free,4):
        mask = bits(pool)-bits(omitted)
        if all(mask&c != c for c in known):
            cases.add(omitted)
    return cases

def check_table(pool, rows):
    counts = Counter()
    for omitted,status in rows:
        a = tuple(sorted(set(pool)-set(omitted)))
        if status=='irreducible':
            assert decide(a)
            assert all(not decide(a[:i]+a[i+1:]) for i in range(len(a)))
            counts['irreducible']+=1
        elif status=='noncover':
            assert not decide(a)
            counts['noncover']+=1
        else:
            assert isinstance(status,int) and status in a
            assert decide(tuple(n for n in a if n!=status))
            counts['proper subcover']+=1
    print(dict(counts),flush=True)

def check_witness(name,size,maximum):
    pairs=read(name)
    ds=[d for d,_ in pairs]
    assert len(pairs)==len(set(ds))==size and max(ds)==maximum
    assert all(0<=r<d for d,r in pairs)
    period=lcm(*ds)
    assert all(any(x%d==r for d,r in pairs) for x in range(period))
    print(name,'all',period,'residues covered',flush=True)
    return set(ds)

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('catalog',help='full-60.json produced by ../reciprocal-sums/saturated60.py')
    args=parser.parse_args()
    data=read('census31-32.json')
    pool=set(data['pool96'])
    rows31=data['size31'];rows32=data['size32']
    assert len(pool)==35
    assert len(rows31)==258 and initial31(pool,args.catalog)=={tuple(ds) for ds,_ in rows31}
    check_table(pool,rows31)
    first=check_witness('witness31-96.jsonl',31,96)
    second=check_witness('witness31-96-second.jsonl',31,96)
    assert {tuple(sorted(pool-first)),tuple(sorted(pool-second))}=={tuple(ds) for ds,s in rows31 if s=='irreducible'}
    # Exactly two noncovering 30-sets of P90, certified by quick30.py.
    p90=pool-{32,96}
    old=[p90-{2,3,t} for t in (4,6)]
    a,b=[x|{32,96} for x in old]
    assert not decide(tuple(sorted(a)))
    assert check_witness('witness32-proper.jsonl',31,96)==b-{90}
    assert not decide(tuple(sorted(a|{105})))
    # These two exceptional rows lack 48 before the extra modulus 105 is added.
    cases={tuple(sorted(pool-(x-{48}|{32,96}))) for x in old}
    cases.update(tuple(ds) for ds,status in rows31 if status=='noncover')
    assert len(rows32)==53 and cases=={tuple(ds) for ds,_ in rows32}
    check_table(pool|{105},rows32)
    check_witness('witness32-upper108.jsonl',32,108)
    check_witness('witness33-upper108.jsonl',33,108)

if __name__=='__main__':
    main()
