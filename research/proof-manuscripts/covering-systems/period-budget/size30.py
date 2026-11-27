"""Only two old configurations at cap 90 can still give a 30-modulus minimum."""
from itertools import combinations
from pathlib import Path
import json
from fixed_sizes import OLD,SEVEN
from crosscheck import decide as old
from mod84 import decide
P=tuple(sorted(OLD+SEVEN+(16,48,60)))
oldsets=[x for x in combinations(P,24) if not old(x)][::-1]
lines=Path('size29-results.txt').read_text().splitlines()
yes=[]; index=0
for line in lines:
    items=line.split()
    if items[2]!='None' or int(items[-1])>index:
        index=int(items[-1]);continue
    A=tuple(sorted(oldsets[int(items[0])-1]+(63,70,72,80,84,90)))
    print('testing',A,flush=True)
    # Try removing a large ternary row first to keep the projection small.
    d=next((d for d in (72,63,9,18,36,45,80,84,70,90,*A) if d in A and decide(tuple(t for t in A if t!=d))),None)
    good=not d and decide(A)
    if good:yes.append(A)
    print('removable',d,'irreducible',good,flush=True)
    Path('size30-yes.json').write_text(json.dumps(yes)+'\n')
