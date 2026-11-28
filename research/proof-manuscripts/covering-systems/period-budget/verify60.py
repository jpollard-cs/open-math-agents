"""Independent verification at sizes 24 and higher."""
from itertools import combinations
from pathlib import Path
import json
from fixed_sizes import OLD,SEVEN,cover
from crosscheck import decide

results=[]
for k in range(24,28):
    for pair in ((),(16,48)):
        for core in combinations(OLD,k-len(SEVEN)-len(pair)):
            A=tuple(sorted(core+pair+SEVEN))
            # All candidates at cap 56 of these sizes must include all 7-rows.
            assert not (decide(A) and all(not decide(A[:i]+A[i+1:]) for i in range(k)))
        for core in combinations(OLD,k-1-len(SEVEN)-len(pair)):
            S=tuple(sorted(core+pair+SEVEN))
            if cover(S):continue
            A=tuple(sorted(S+(60,)))
            if cover(A) and all(not cover(A[:i]+A[i+1:]) for i in range(k)):
                results.append(A)
    print("size",k,"cap 56 clear; cap 60 irreducible",sum(len(a)==k for a in results),flush=True)
assert {tuple(a) for a in json.loads(Path("cap60-crosscheck.json").read_text())}==set(results)
print("All cap-60 lists at sizes 24 and higher agree exactly between the two solvers.")
