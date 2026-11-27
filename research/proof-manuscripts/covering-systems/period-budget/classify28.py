"""Search 28-sets containing all five new moduli at cap 84."""
from itertools import combinations
from pathlib import Path
from mod84 import decide
from fixed_sizes import OLD,SEVEN
from crosscheck import decide as old
import sys,json
P=tuple(sorted(OLD+SEVEN+(16,48,60)))
known=json.loads(Path('size29-yes.json').read_text())[0]
todo=[]
for om in combinations(P,4):
    X=tuple(d for d in P if d not in om)
    if old(X):continue
    A=tuple(sorted(X+(63,70,72,80,84)))
    if set(A)<=set(known) or sum(d in A for d in (16,48,80))==1:continue
    todo.append((om,A))
# Larger possible minimum first, then cases close to the size-29 obstructions.
todo.sort(key=lambda a:(a[1][0],len(set(a[0])&{2,4,6,9,24,36}),a[0]),reverse=True)
print('candidates',len(todo),flush=True)
all_yes=[]
for i,(om,A) in enumerate(todo):
    d=next((d for d in (84,80,72,70,63,2,3,4,5,6,7,*A) if d in A and decide(tuple(t for t in A if t!=d))),None)
    if d is None and decide(A):
        all_yes.append(A)
        print('extremizer omits',om,flush=True)
Path('all-five-extremizers-28.json').write_text(json.dumps(all_yes)+'\n')
print('total',len(all_yes))
