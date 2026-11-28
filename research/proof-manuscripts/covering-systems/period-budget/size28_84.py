"""Seek sharp size 28 examples at cap 84; all four-extra branches use 24 old rows."""
from itertools import combinations
from pathlib import Path
from mod84 import decide
from fixed_sizes import OLD, SEVEN
from crosscheck import decide as old
import json
P=tuple(sorted(OLD+SEVEN+(16,48,60)))
oldsets=[x for x in combinations(P,24) if not old(x)][::-1]
assert len(oldsets)==35
yes=[]
for miss in (80,72,70,63):
    others=tuple(d for d in (63,70,72,80,84) if d!=miss)
    for number,X in enumerate(oldsets):
        A=tuple(sorted(X+others))
        if sum(d in A for d in (16,48,80))==1:continue
        removable=next((d for d in (84,80,72,70,63,2,3,4,5,6,7,*A) if d in A and decide(tuple(t for t in A if t!=d))),None)
        if not removable and decide(A):
            yes.append(A)
            Path('examples28_84.json').write_text(json.dumps(yes)+'\n')
        print(miss,number+1,'removable',removable,'total',len(yes),flush=True)
