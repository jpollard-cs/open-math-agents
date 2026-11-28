"""Replay local Hall bounds and check donor allocations with independent integer sums."""
from bisect import bisect_right
from itertools import combinations, product
from math import ceil, isqrt, log, prod, sqrt


def primes_to(n):
    flags=bytearray([1])*(n+1)
    flags[:2]=bytes(2)
    for r in range(2,isqrt(n)+1):
        if flags[r]:
            flags[r*r::r]=bytes((n-r*r)//r+1)
    return [r for r in range(2,n+1) if flags[r]]


def verify_local_matching(radices):
    points=list(product(*(range(p) for p in radices)))
    full=(1<<len(points))-1
    boxes=[]
    for pattern in product(*(range(-1,p) for p in radices)):
        support=sum(1<<i for i,v in enumerate(pattern) if v!=-1)
        if support:
            mask=sum(1<<j for j,pt in enumerate(points)
                     if all(x==-1 or x==y for x,y in zip(pattern,pt)))
            boxes.append((mask,support))
    containing=[[i for i,(m,_) in enumerate(boxes) if m>>j&1] for j in range(len(points))]
    visited=set()
    critical=[]
    def dfs(selected,covered):
        if selected in visited:
            return
        visited.add(selected)
        if covered==full:
            critical.append(selected)
            return
        hole=(~covered & full) & -(~covered & full)
        for row in containing[hole.bit_length()-1]:
            extended=selected|{row}
            seen=0
            twice=0
            for i in extended:
                mask=boxes[i][0]
                twice |= seen & mask
                seen |= mask
            if all(boxes[i][0] & ~twice for i in extended):
                dfs(extended,seen)
    dfs(frozenset(),0)
    cuts=0
    for F in critical:
        rows=[boxes[i][1] for i in F]
        active=0
        for s in rows:
            active|=s
        capacities=[p-1 if active>>i&1 else 0 for i,p in enumerate(radices)]
        slots=[i for i,c in enumerate(capacities) for _ in range(c)]
        # Independent augmenting-path algorithm checks Hall after every reservation.
        for reserved in range(len(rows)):
            pairs={}
            def augment(slot,seen):
                for row,S in enumerate(rows):
                    if row==reserved or row in seen or not S>>slots[slot]&1:
                        continue
                    seen.add(row)
                    if row not in pairs or augment(pairs[row],seen):
                        pairs[row]=slot
                        return True
                return False
            assert all(augment(slot,set()) for slot in range(len(slots)))
            for small in range(1<<len(radices)):
                big=active & ~small
                free=0
                groups=[0]*len(radices)
                for i,S in enumerate(rows):
                    if i==reserved:
                        continue
                    B=S&big
                    if B==0:
                        free+=1
                    elif B.bit_count()==1:
                        groups[B.bit_length()-1]+=1
                excess=free+sum(max(0,w-c) for w,c in zip(groups,capacities))
                delta=len(F)-1-len(slots)
                assert excess<=delta+sum(c for i,c in enumerate(capacities) if small>>i&1)
                cuts+=1
    return len(critical),cuts


def verify_allocation(y,gs):
    D=log(y)
    b=ceil(log(D))
    a=int(y/sqrt(D))
    E=gs[bisect_right(gs,a):bisect_right(gs,y)]
    transfers=[r-1-ceil(r/sqrt(D)) for r in E]
    H=sum(transfers)
    n=H//((4*b+2)*y)
    Q=gs[bisect_right(gs,4*y):][:n]
    assert len(Q)==n and n>0
    received=[0]*n
    start=0
    m=10**9
    M=0
    for r,h in zip(E,transfers):
        floor,rem=divmod(h,n)
        detail=[floor+int((i-start)%n<rem) for i in range(n)]
        assert sum(detail)==h and h+ceil(r/sqrt(D))==r-1
        m=min(m,min(detail)); M=max(M,max(detail))
        for i,v in enumerate(detail):
            received[i]+=v
        start=(start+rem)%n
    assert sum(received)==H and max(received)-min(received)<=1
    # An entirely separate round-robin calculation: row i is the i-th
    # residue of a length-H interval, so all column sums are known exactly.
    assert received==[H//n+int(i<H%n) for i in range(n)]
    assert m>1
    for q,t in zip(Q,received):
        orig=q-1+t
        for omitted in (0,1,q//4,q//4+1):
            w=orig-omitted
            assert w//q==b+1
            assert orig-(b+1)*q<q-1
            assert w-q+1==t-omitted
            # A half-donor batch must test at least this many distinct r's.
            assert (q//2+M-1)//M>=2
    return n,len(E),H,m,M


if __name__=='__main__':
    for radices in ((2,2),(2,3),(2,2,2)):
        print('grid, irredundant labelled placements, reservation/cut checks',
              radices,*verify_local_matching(radices))
    values=(1024,4096,12000,32000,70000,120000)
    gs=primes_to(5*max(values))
    for y in values:
        print('y, recipients, donors, donated rows, min/max per edge:',
              y,*verify_allocation(y,gs))
