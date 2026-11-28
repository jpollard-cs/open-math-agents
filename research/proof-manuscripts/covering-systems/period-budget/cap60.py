"""Find extremizers of size >=24 up to the next change of modulus pool."""
from itertools import combinations
from pathlib import Path
import json
from crosscheck import decide
from fixed_sizes import OLD,SEVEN

def run():
    rows=[]
    # At size 24 or above, all seven 7-rows are necessary by the top-digit test.
    # The only extension of the cap-59 pool is modulus 60.
    for k in range(24,28):
        for pair in ((),(16,48)):
            fixed=SEVEN+pair+(60,)
            for core in combinations(OLD,k-len(fixed)):
                A=tuple(sorted(fixed+core))
                if decide(A) and all(not decide(A[:i]+A[i+1:]) for i in range(k)):
                    rows.append(A)
        good=[v for v in rows if len(v)==k]
        print(k,len(good),good[:1],flush=True)
    Path("cap60-crosscheck.json").write_text(json.dumps(rows)+"\n")

if __name__=="__main__":run()
