"""Independent small-shape tests for the sliding-row theorem and four-copy census."""
from itertools import combinations
from math import gcd
from functools import lru_cache

STEPS = [(0, 1), (1, 0), (-1, 0), (0, -1)]
def normalize(cells):
    x0, y0 = min(x for x, _ in cells), min(y for _, y in cells)
    return tuple(sorted((x-x0, y-y0) for x,y in cells))

def add_cell(shapes):
    return {normalize(set(shape) | {(x+u,y+v)})
            for shape in shapes for x,y in shape for u,v in STEPS
            if (x+u,y+v) not in shape}

def periods(index):
    for a in range(1, index+1):
        if index % a == 0:
            for shear in range(a):
                yield a, index//a, shear

def residues(shape, lattice):
    a,b,shear = lattice
    return {((x - (y//b)*shear) % a, y % b) for x,y in shape}

def four_pack(shape):
    n = 4*len(shape)+3
    for lat in periods(n):
        a,b,_ = lat
        image = residues(shape, lat)
        if len(image) != len(shape):
            continue
        diff = residues([(x-u,y-v) for x,y in image for u,v in image],lat)
        acceptable = [(x,y) for x in range(a) for y in range(b) if (x,y) not in diff]
        for j,p in enumerate(acceptable):
            near = [q for q in acceptable[j+1:]
                    if not (residues([(q[0]-p[0],q[1]-p[1])],lat) & diff)]
            for u,v in combinations(near,2):
                if not (residues([(u[0]-v[0],u[1]-v[1])],lat) & diff):
                    return True
    return False

def row_checks(shape):
    diff = {(x-u,y-v) for x,y in shape for u,v in shape}
    vectors = {(x+u,y+v) for x,y in diff for u,v in STEPS}
    cases = 0
    for vx,vy in vectors:
        if (vx,vy) <= (0,0):
            continue
        d = gcd(vx,vy)
        px,py = vx//d,vy//d
        # Pick an integer vector transverse to the primitive row.
        ux,uy = next((i,j) for i in range(-9,10) for j in range(-9,10)
                     if px*j-py*i == 1)
        blocked = {((x*uy-y*ux)%d, px*y-py*x) for x,y in diff}
        if any((x,y)!=(0,0) and (x*uy-y*ux)%d == 0 and px*y==py*x
               for x,y in diff):
            continue
        cases += 1
        assert all((i,0) in blocked for i in range(d))
        width = max(j for i,j in blocked)
        gap, offset = next((j,i) for j in range(1,width+2) for i in range(d)
                           if (i,j) not in blocked)
        for t in range(1,width//gap+1):
            assert ((offset*t)%d, gap*t) not in blocked
        # Separate exhaustive maximum independent set on a small finite cylinder.
        height = min(6, width+3)
        if d*height>16:
            continue
        vertices = [(i,j) for i in range(d) for j in range(height)]
        conflict = []
        for i,j in vertices:
            conflict.append(sum(1<<k for k,(u,v) in enumerate(vertices)
                                if ((u-i)%d,v-j) in blocked))
        @lru_cache(None)
        def alpha(mask):
            if not mask:
                return 0
            low = mask & -mask
            return max(alpha(mask ^ low), 1+alpha(mask & ~conflict[low.bit_length()-1]))
        assert alpha((1<<len(vertices))-1) == 1+(height-1)//gap
    return cases

if __name__ == '__main__':
    shapes={((0,0),)}
    for size in range(1,9):
        nontiles=checks=0
        for shape in shapes:
            checks += row_checks(shape)
            if all(len(residues(shape,l))<size for l in periods(size)):
                nontiles+=1
                assert not four_pack(shape)
        print(size,len(shapes),nontiles,checks,flush=True)
        if size!=8:
            shapes=add_cell(shapes)
