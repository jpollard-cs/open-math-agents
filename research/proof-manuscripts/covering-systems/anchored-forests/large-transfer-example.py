"""Exact compressed specification and arithmetic checks for the y=12,000 cover.

python large-transfer-example.py              # summary and verification
python large-transfer-example.py --row 1000  # modulus and aligned residue by row index

Integer radices and (integer) ceilings are fixed below, independently of any
floating-point logarithms in the asymptotic construction.  No huge integer
period or expanded multi-billion-row list is needed for the summary.
"""
import argparse
from bisect import bisect_right
from math import isqrt


def primes_to(n):
    sieve=bytearray([1])*(n+1)
    sieve[:2]=bytes(2)
    for p in range(2,isqrt(n)+1):
        if sieve[p]:
            sieve[p*p::p]=bytes((n-p*p)//p+1)
    return [i for i,valid in enumerate(sieve) if valid]


def ceil_div(a,b):
    return (a+b-1)//b


def stages():
    # Rational divisor near sqrt(log(12000)). All assertions below are exact.
    y=12000
    a=3915
    z=500009
    gs=primes_to(z)
    assert gs[-1]==z
    E=[r for r in gs if a<r<=y]
    Q=gs[bisect_right(gs,4*y):][:28]
    assert len(Q)==28
    regular={r:ceil_div(100*r,306) for r in E}
    per_owner=[0]*len(Q)
    left=0
    distributed={}
    for r in E:
        base,remainder=divmod(r-1-regular[r],len(Q))
        widths=[base+int((j-left)%len(Q)<remainder) for j in range(len(Q))]
        assert regular[r]+sum(widths)==r-1 and regular[r]<r
        distributed[r]=widths
        for j,w in enumerate(widths):
            per_owner[j]+=w
        left=(left+remainder)%len(Q)
    lo=min(min(w) for w in distributed.values())
    hi=max(max(w) for w in distributed.values())
    # Old guards through 6y are precisely the a-smooth integers there.
    mask=bytearray([1])*(6*y+1)
    for r in gs[bisect_right(gs,a):bisect_right(gs,6*y)]:
        mask[r::r]=bytes((6*y)//r)
    old=[d for d in range(1,6*y+1) if mask[d]]
    assert len(old)>=max(Q)-1 and 6*y<z
    assert hi<=a and Q[-1]*y*hi<z*z and Q[-1]*old[Q[-1]-2]<z*z
    assert a*a>z
    assert all((q-1+h-1-q//4)//q==4 and (q-1+h)//q==4 and q-1+h-4*q<q-1
               for q,h in zip(Q,per_owner))
    # If a batch contains at least half donor rows it sees this many donor
    # digits, each with at least lo+1 surviving children.
    distinct=min(ceil_div(ceil_div(q,2),hi) for q in Q)
    extra=6*(z//6+1)
    assert extra>z and extra//2<z
    positions=[]
    for p in gs:
        power=p
        while power<=z:
            positions.append((p,power))
            power*=p
    recipients=set(Q)
    donors=set(E)
    kinds=[('ordinary',p,h) for p,h in positions if p<=a]
    kinds.extend(('recipient',q,q) for q in Q)
    kinds.extend(('donor',r,r) for r in E)
    initial={(p,h) for _,p,h in kinds}
    kinds.extend(('ordinary',p,h) for p,h in positions if (p,h) not in initial and p!=z)
    kinds.append(('terminal',z,z))
    assert len(kinds)==len(positions) and {(p,h) for _,p,h in kinds}==set(positions)
    used={}
    for kind,p,h in kinds:
        assert h==p*used.get(p,1)
        used[p]=h
    size=1+sum(p-1 for p,h in positions)
    # Count again by sieving the greatest prime factor of each integer.
    # An integer h contributes its base minus one precisely if h is a power.
    greatest=[0]*(z+1)
    for p in gs:
        greatest[p::p]=[p]*(z//p)
    second=1
    for h in range(2,z+1):
        p=greatest[h]
        v=h
        while v%p==0:
            v//=p
        if v==1:
            second+=p-1
    assert second==size
    assert size==sum(p-1 if kind!='terminal' else p for kind,p,h in kinds)
    summary=dict(donors=len(donors),recipients=len(recipients),size=size,cap=z*extra,
                 allocated=sum(per_owner),lo=lo,hi=hi,distinct=distinct,
                 batches=3*len(Q),first_q=Q[0],last_q=Q[-1])
    return summary,kinds,regular,distributed,Q,old,extra


def lookup(index,data):
    info,kinds,regular,distributed,Q,old,extra=data
    if not 0<=index<info['size']:
        raise ValueError('row index must lie between zero and size-1')
    earlier=[]
    for kind,p,h in kinds:
        count=p if kind=='terminal' else p-1
        if index>=count:
            earlier.append(p)
            index-=count
            continue
        label=index+1
        if kind=='recipient':
            modulus=p*old[index]
        elif kind=='donor' and index>=regular[p]:
            j=index-regular[p]
            for q,width in zip(Q,distributed[p]):
                if j<width:
                    modulus=p*q*(j+1)
                    break
                j-=width
        elif kind=='terminal' and label==p:
            modulus=p*extra
        else:
            modulus=h*label
        # Aligned phase: previous period times the nonzero new label,
        # or the zero label at the terminal. Work modulo the requested row.
        phase=label%modulus
        for radix in earlier:
            phase=phase*radix%modulus
        return modulus,phase
    raise AssertionError('stage count mismatch')


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--row',type=int)
    args=ap.parse_args()
    data=stages()
    info=data[0]
    print(info)
    if args.row is not None:
        print('modulus, aligned residue',lookup(args.row,data))
    else:
        print('first and last row',lookup(0,data),lookup(info['size']-1,data))
