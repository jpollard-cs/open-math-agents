"""Count optimal T-packings directly on every relevant HNF torus."""
from math import gcd
from verify import periods

def primitive_necklaces(colors, length):
    counts = {}
    for n in range(1,length+1):
        counts[n] = colors**n - sum(counts[d] for d in counts if n%d==0)
    return counts[length]//length

def count_patterns(w,h,k):
    rect = [(x,y) for x in range(w) for y in range(h)]
    shape = {(0,y) for y in range(2*h-1)} | {(x,h-1) for x in range(w)}
    total=0
    for a,b,shear in periods(w*h*k):
        def label(x,y):
            r=y%b
            return r*a+(x-(y//b)*shear)%a
        n=a*b
        def translate(mask,i):
            return sum(1<<label(z%a+i%a,z//a+i//a) for z in range(n) if mask>>z&1)
        def image(cells):
            return sum(1<<z for z in {label(x,y) for x,y in cells})
        root_rect,root_shape=image(rect),image(shape)
        if root_rect.bit_count()!=w*h or root_shape.bit_count()!=len(shape):
            continue
        shadows=[translate(root_rect,i) for i in range(n)]
        occupied=[translate(root_shape,i) for i in range(n)]
        through=[[i for i in range(n) if shadows[i]>>z&1] for z in range(n)]
        full=(1<<n)-1
        cases=set()
        def visit(rmask,smask,centers):
            if rmask==full:
                orbit={translate(centers,i) for i in range(n)}
                if len(orbit)==n:cases.add(min(orbit))
                return
            uncovered=full^rmask
            z=(uncovered&-uncovered).bit_length()-1
            for i in through[z]:
                if not (shadows[i]&rmask or occupied[i]&smask):
                    visit(rmask|shadows[i],smask|occupied[i],centers|(1<<i))
        visit(shadows[0],occupied[0],1)
        total+=len(cases)
    return total

if __name__=='__main__':
    for w,h in [(2,2),(3,2),(3,3),(4,2)]:
        for k in range(1,7):
            count=count_patterns(w,h,k)
            assert count==primitive_necklaces(w-1,k)
            print(w,h,k,count,flush=True)
