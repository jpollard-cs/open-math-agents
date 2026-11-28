"""Recompute one-digit gluing from brute-force row placements."""
from functools import cache
from itertools import combinations_with_replacement, product


@cache
def profiles(q, r, supports):
    full = (1 << (q*r))-1
    holes = {full}
    for support in supports:
        masks = {(x if support & 1 else -1, y if support & 2 else -1)
                 for x,y in product(range(q),range(r))}
        classes = [sum(1 << (y*q+x) for x,y in product(range(q),range(r))
                       if (a in (-1,x) and b in (-1,y))) for a,b in masks]
        holes = {old & ~mask for old,mask in product(holes,classes)}
    return {tuple(sum((m >> (y*q+x)) & 1 for y in range(r)) for x in range(q)) for m in holes}


@cache
def quota(q,r,rows):
    return min(sum(v>0 for v in profile) for profile in profiles(q,r,rows))


@cache
def local_min(q,r,rows):
    return min(map(sum, profiles(q,r,rows)))


@cache
def rigid(q,r,rows):
    return local_min(q,r,rows)==1 and all(local_min(q,r,rows[:i]+rows[i+1:])>=2
                                           for i in range(len(rows)))


@cache
def joint_min(q,r,s,left,right):
    return min(sum(a*b for a,b in zip(x,y))
               for x,y in product(profiles(q,r,left),profiles(q,s,right)))


def run(q,r,s,bound):
    families = [t for n in range(bound+1) for t in combinations_with_replacement((1,2,3),n)]
    tested = positive = 0
    for left,right in product(families,repeat=2):
        a = quota(q,r,left)
        b = quota(q,s,right)
        local = (a+b==q+1 and rigid(q,r,tuple(sorted(left+(1,)*(a-1))))
                 and rigid(q,s,tuple(sorted(right+(1,)*(b-1)))))
        actual = joint_min(q,r,s,left,right) == 1
        actual = actual and all(joint_min(q,r,s,left[:i]+left[i+1:],right)>=2 for i in range(len(left)))
        actual = actual and all(joint_min(q,r,s,left,right[:i]+right[i+1:])>=2 for i in range(len(right)))
        assert local==actual,(q,r,s,left,right)
        tested += 1
        positive += actual
    print((q,r,s,bound), tested, "pairs,", positive, "irreducible")


if __name__ == "__main__":
    run(2,2,2,4)
    run(3,2,2,4)
    run(2,2,3,4)
