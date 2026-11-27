"""All candidates at 27 pass through the noncoverable 26-subsets at cap 70."""
import ast,json
from pathlib import Path
from itertools import combinations
from fast72 import exact
from fixed_sizes import SEVEN,OLD
from crosscheck import decide
def candidates():
    P=tuple(sorted(SEVEN+OLD+(16,48,60)))
    assert all(decide(x) for x in combinations(P,25))
    return [tuple(sorted(A+(72,))) for A in ast.literal_eval(Path('cap70-checks.txt').read_text().splitlines()[-1]) if (16 in A)==(48 in A)]
if __name__=='__main__':
    yes=[]
    for i,A in enumerate(candidates()):
        removable=next((d for d in (72,70,63,3,4,5,6,7,*A) if d in A and exact(tuple(t for t in A if t!=d))),None)
        if not removable and exact(A):yes.append(A)
        Path('size27-yes.json').write_text(json.dumps(yes)+'\n')
        print(i+1,'removable',removable,'irreducible total',len(yes),flush=True)
