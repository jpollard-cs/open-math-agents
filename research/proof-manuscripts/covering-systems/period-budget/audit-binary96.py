"""Exhaustively compare projected binary masks with each claimed family."""
from itertools import combinations,product
from decide96 import binary_choices
from witness96 import virtual
N=120
FULL=(1<<N)-1

def shift(mask,r):
    return ((mask<<r)&FULL)|(mask>>(N-r))

def verify(ds):
    actual=set()
    # Translate the first residue to 0 and designate its side as 0.
    for rs in product((0,),*(range(d) for d in ds[1:])):
        rows=[sum(1<<x for x in range(r,N,d)) for d,r in zip(ds,rs)]
        for sides in product((0,),*((0,1) for _ in ds[1:])):
            pair=[0,0]
            for b,m in zip(sides,rows):pair[b]|=m
            actual.add(pair[0]&pair[1])
    actual={shift(m,r) for m in actual for r in range(N)}
    predicted=set()
    for family in binary_choices(ds):
        possibilities=[{sum(1<<x for x in range(N) if virtual(d,r,x)) for r in range(d if d>0 else N)} for d in family]
        unions={0}
        for options in possibilities:unions={a|b for a in unions for b in options}
        predicted.update(unions)
    assert predicted<=actual
    assert all(any(a&b==a for b in predicted) for a in actual)
    print(ds,len(actual),len(predicted))

if __name__=='__main__':
    ds=(8,24,24,40)
    for n in range(1,5):
        for sub in sorted(set(combinations(ds,n))):
            verify(sub)
