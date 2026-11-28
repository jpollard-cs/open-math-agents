"""Compute the optimizer count from differences and independently enumerate small tori."""
from verify import add_cell
from t_families import count_patterns, primitive_necklaces

def phases(diff,period,separation):
    if any(x and y==0 and x%period==0 for x,y in diff):
        return set()
    forbidden={x%period for x,y in diff if y==separation}
    return set(range(period))-forbidden

def counts(shape,w,h,k):
    diff={(x-u,y-v) for x,y in shape for u,v in shape}
    if not all((i,j) in diff for i in range(1-w,w) for j in range(1-h,h)):
        raise ValueError("rectangle differences are not contained in shape differences")
    row=phases(diff,w,h)
    column=phases({(y,x) for x,y in diff},h,w)
    assert (0 in row)==(0 in column)
    return (primitive_necklaces(len(row),k)+primitive_necklaces(len(column),k)
            -int(k==1 and 0 in row))

if __name__=='__main__':
    shapes={((0,0),)}
    for s in range(1,8):
        tests=0
        for shape in sorted(shapes):
            diff={(x-u,y-v) for x,y in shape for u,v in shape}
            for w in range(2,5):
                for h in range(2,5):
                    if s>w*h or not all((i,j) in diff for i in range(1-w,w)
                                        for j in range(1-h,h)):
                        continue
                    for k in (1,2,3):
                        assert count_patterns(w,h,k,shape)==counts(shape,w,h,k)
                        tests+=1
        print(s,tests,flush=True)
        shapes=add_cell(shapes)
