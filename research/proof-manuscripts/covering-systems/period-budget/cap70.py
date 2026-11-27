"""Sufficient subcover tests, plus exact elimination of one additional row."""
from itertools import combinations
from math import lcm
from crosscheck import decide,decide_base
from fixed_sizes import OLD,SEVEN
from functools import cache

@cache
def small_certificate(A):
    """Discard excess top 7-rows, retaining any seven that certify a cover."""
    seven=tuple(d for d in A if d%7==0)
    remain=[d for d in A if d%7]
    pair=[d for d in remain if d%16==0]
    remain=[d for d in remain if d%16]
    if len(pair)==2:remain.append(24)
    if decide_base(tuple(sorted(remain))):return True
    for ids in combinations(seven,7):
        v=lcm(*(s//7 for s in ids))
        # v can include the top 3-adic digit and yield five such rows.
        if v%9 and 120%v==0 and decide_base(tuple(sorted(remain+[v]))):return True
        if v%9==0 and sum(d%9==0 for d in remain)<=3 and (v//3 and 120%(v//3)==0) and decide_base(tuple(sorted(remain+[v]))):return True
    return False

if __name__=='__main__':
    P=tuple(sorted(OLD+SEVEN+(16,48,60)))
    assert len(P)==27
    assert all(decide(A) for A in combinations(P,25))
    print("Every one of the 351 old 25-subsets is coverable. This excludes size 26 through cap 69.",flush=True)
    pending=[]
    for A in combinations(P,24):
        if decide(A): continue
        B=tuple(sorted(A+(63,70)))
        if any(small_certificate(B[:i]+B[i+1:]) for i in range(26)):continue
        pending.append(B)
    print("Size-26 sets still requiring a full multi-row test at cap 70:",len(pending),flush=True)
    print(pending)
