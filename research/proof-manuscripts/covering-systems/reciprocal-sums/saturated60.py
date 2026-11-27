"""Enumerate sets at cap 60 for which the prime 7 is either absent or saturated."""
from pathlib import Path
from math import lcm
import json
import enumerate_covers as general
from section_solver import reduced

def run():
    ordinary = [n for n in general.modulus_pool(60) if n%7]
    seven = [n for n in general.modulus_pool(60) if n%7==0]
    assert seven == [7,14,21,28,35,42,56]
    assert lcm(*(n//7 for n in seven)) == 120 and 120 not in ordinary
    general.can_cover=reduced
    catalogs=[[],[]]
    for with_seven in range(2):
        yes=bytearray(1 << len(ordinary))
        pos={d:i for i,d in enumerate(ordinary)}
        for row in catalogs[0]:
            mask=sum(1 << pos[d] for d in row)
            yes[mask]=1
        for mask in range(len(yes)):
            if yes[mask]:
                continue
            rest=mask
            while rest:
                bit=rest & -rest
                if yes[mask^bit]:
                    yes[mask]=1
                    break
                rest ^= bit
            if yes[mask]:
                continue
            row=tuple(d for i,d in enumerate(ordinary) if mask & (1<<i))
            candidate=(*row,120) if with_seven else row
            period=lcm(*candidate)
            if sum(period//d for d in candidate)<period: continue
            if any(sum(d%power==0 for d in candidate)<p for p,power in general.prime_powers(period)): continue
            if reduced(candidate):
                yes[mask]=1
                catalogs[with_seven].append(sorted([*row,*seven]) if with_seven else list(row))
        print('seven' if with_seven else 'ordinary',len(catalogs[with_seven]),flush=True)
    return catalogs[0]+catalogs[1]
if __name__=='__main__':
    rows=run()
    Path('full-60.json').write_text(json.dumps(rows))
    print(len(rows),{k:min(s[-1] for s in rows if len(s)==k) for k in sorted(set(map(len,rows)))})
