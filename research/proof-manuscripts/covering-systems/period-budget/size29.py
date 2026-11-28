"""At 29 and cap 84 only the old noncoverable 24-sets and all five new rows can work."""
from itertools import combinations
from pathlib import Path
from mod84 import decide
from fixed_sizes import OLD, SEVEN
from crosscheck import decide as old
import json
P=tuple(sorted(OLD+SEVEN+(16,48,60)))
# The 35 cap-80 rows are enumerated in reverse order in the recorded last run.
oldsets=[x for x in combinations(P,24) if not old(x)][::-1]
lines=Path('size28-reverse.txt').read_text().splitlines()
assert len(lines)==len(oldsets)==35
yes=[]
for X,line in zip(oldsets,lines):
    if "removable None" not in line:continue
    A=tuple(sorted(X+(63,70,72,80,84)))
    removable=next((d for d in (84,80,72,70,63,2,3,4,5,6,7,*A) if d in A and decide(tuple(t for t in A if t!=d))),None)
    if not removable and decide(A):yes.append(A)
    Path('size29-yes.json').write_text(json.dumps(yes)+'\n')
    print(line.split()[0],'removable',removable,'irreducible total',len(yes),flush=True)
