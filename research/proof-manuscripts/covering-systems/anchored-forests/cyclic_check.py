"""Direct enumeration of binary diamonds and of arbitrary two-link residual relations."""
from itertools import combinations,product
from collections import Counter
from fractions import Fraction as F
from diamond_gain import select

def check_binary():
    edges=((0,2),(2,1),(1,3),(3,0),(0,1))
    pts=list(product(range(2),repeat=4))
    hist=[Counter() for _ in range(6)]
    for labels in product(tuple(product(range(2),repeat=2)), repeat=5):
        for skip in range(6):
            hist[skip][sum(all(j==skip or (x[u],x[v])!=t
                          for j,((u,v),t) in enumerate(zip(edges,labels))) for x in pts)]+=1
    assert [min(h) for h in hist]==[3,3,3,3,2,1]
    print('1024 arbitrary binary assignments; minimum holes', [min(h) for h in hist],
          'unique-hole assignments', hist[5][1])

def check_paths(d):
    N=d*d
    rows=[sum(1<<i for i in c) for k in range(d) for c in combinations(range(N),k)]
    mask=(1<<d)-1
    slices=[[(r>>(i*d))&mask for i in range(d)] for r in rows]
    # Both relations are stored with their endpoint first.
    off=[sum(1<<(d*u+v) for u in range(d) for v in range(d) if u!=a and v!=b)
         for a in range(d) for b in range(d)]
    rigid=0; sharp=0
    for l in slices:
        for r in slices:
            forb=0; singles=[]
            for a,la in enumerate(l):
                for b,rb in enumerate(r):
                    sz=d-(la|rb).bit_count()
                    if sz==0:forb|=1<<(d*a+b)
                    if sz==1:singles.append(d*a+b)
            assert forb.bit_count()<=d-1
            assert all(not (off[i]&forb) for i in singles)
            rigid+=bool(singles);sharp+=forb.bit_count()==d-1
    print(f'd={d}: {len(rows)**2} two-link profiles, {rigid} with a singleton fibre, {sharp} at the missing-pair bound')

def weight_check():
    # Second computation. Trial-divide every candidate cofactor by all primes
    # below the first vertex, and subtract exact full harmonic sums.
    def smallprimes(n):
        return [i for i in range(2,n+1) if all(i%j for j in range(2,int(i**.5)+1))]
    groups=select(300)[1]
    total=F(0)
    for ps in groups:
        prime_basis=smallprimes(ps[0]-1)
        allowed=[]
        for a in range(1,2*ps[0]):
            n=a
            for p in prime_basis:
                while n%p==0:n//=p
            if n==1:allowed.append(a)
        for p in ps:
            assert len(allowed)>=p-2
            total+=sum((F(1,p*d) for d in allowed[:p-2]),F())-sum((F(1,p*d) for d in range(1,p)),F())
        for i,j in ((0,2),(2,1),(1,3),(3,0),(0,1)):
            total+=F(1,ps[i]*ps[j])
    assert total>F(587276817,10**12)
    print('independent full reciprocal check of 12 disjoint diamonds through 300:',float(total))
    print(groups)

if __name__=='__main__':
    check_binary()
    for d in (2,3,4):check_paths(d)
    weight_check()
