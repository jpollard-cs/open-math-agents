"""Verify the exact four-row hole classification on its 120-point period."""
from itertools import combinations, product
from functools import cache
N=120
full=(1<<N)-1
@cache
def row(d,r):return (full//((1<<d)-1)) << r
def rot(mask,s):return ((mask<<s)&full)|(mask>>(N-s))
masks=set()
# Translate the 8-row to residue zero and swap the binary labels to its side.
for r1,r2,r3 in product(range(24),range(24),range(40)):
    aa,bb,cc=row(24,r1),row(24,r2),row(40,r3)
    for sides in product(range(2),repeat=3):
        buckets=[row(8,0),0]
        for side,cl in zip(sides,(aa,bb,cc)):buckets[side]|=cl
        masks.add(buckets[0]&buckets[1])
actual={rot(s,r) for s in masks for r in range(N)}
predicted=set()
for i in range(8):
    for a,b in combinations(range(i,24,8),2):
        for c in range(i,40,8):predicted.add(row(24,a)|row(24,b)|row(40,c))
for r,s in product(range(24),range(40)):
    if r%8!=s%8:predicted.add(row(24,r)|row(40,s))
assert predicted<=actual
assert all(any(s&p==s for p in predicted) for s in actual)
assert all(not any(p!=q and p&q==p for q in predicted) for p in predicted)
print(len(actual),'attainable masks;',len(predicted),'distinct maximal masks.')
