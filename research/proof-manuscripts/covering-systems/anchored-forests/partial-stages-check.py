"""Two independent computations of the retained 5-by-11 projection."""
from itertools import product
from math import gcd,lcm,prod

old_divs=(1,2,3,4,6,8,9,12,18,24,36,72)
stages=[(2,[2]),(2,[4]),(2,[8]),(3,[3,6]),(3,[9,18]),
        (13,[13*d for d in old_divs])]
# At 11, row 55 makes the available labels depend on the earlier label at 5.
for r,u in ((5,4),(7,6),(11,5)):
    stages.append((r,[r*d for d in range(1,r-u)]+[13*r*d for d in old_divs[:u]]))
stages += [(2,[16]),(17,[17*d for d in [*range(1,17),18]])]


def check_stage_and_scan():
    phases={}
    L=1
    for i,(r,rows) in enumerate(stages):
        final=(i==len(stages)-1)
        assert len(rows)==r-1+final
        assert all(lcm(n,L)==L*r for n in rows)
        if final:
            assert lcm(*(gcd(n,L) for n in rows))==L
        for j,n in enumerate(rows):
            assert n not in phases
            phases[n]=L*(j+1)%n
        L*=r
    assert (len(phases),L)==(57,12252240)
    coverage=bytearray(L)
    for n,a in phases.items():
        coverage[a::n]=bytes([1])*(L//n)
    assert all(coverage)
    special={r:{n for n in stages[i][1] if n%13==0}
             for i,r in ((6,5),(7,7),(8,11))}
    single=stages[5][1]
    A=special[5] | special[11] | set(single[:4])
    B=special[7] | set(single[4:11])
    assert (len(A),len(B),len(A&B))==(13,13,0)
    # One ordinary p-row outside the two batches. Reserve terminal 17.
    # Align ordinary 11 rows on four distinct labels; row 55 forbids
    # just one extra (5,11) pair above the aligned old residue.
    for i,d in enumerate((1,2,3,4)):
        phases[11*d]=next(x for x in range(11*d) if x%d==0 and x%11==i)
    phases[55]=next(x for x in range(55) if x%5==0 and x%11==4)
    subset=bytearray(L)
    for n,a in phases.items():
        if n not in A|B|{17}:
            subset[a::n]=bytes([1])*(L//n)
    projections=[]
    for batch in (A,B):
        guard=lcm(*(n//13 for n in batch))
        projections.append(sum(0 in subset[u::guard] for u in range(guard)))
    assert projections==[34,7]
    return max(phases),projections


def exhaustive_grid():
    full=(1<<55)-1
    col=[sum(1<<(11*i+j) for i in range(5)) for j in range(11)]
    # Arbitrary assignments to four universal 11-labels plus one pair.
    # Missing ordinary tests only enlarge the residual grid.
    mins=[55,55,55]
    cases=0
    for a,b,c,d in product(col,repeat=4):
        base=full & ~(a|b|c|d)
        for i in range(55):
            rem=base & ~(1<<i)
            mins[0]=min(mins[0],rem.bit_count())
            seen_cols=0
            seen_rows=0
            for j in range(5):
                segment=rem>>(11*j)&2047
                seen_cols|=segment
                seen_rows+=bool(segment)
            mins[1]=min(mins[1],seen_cols.bit_count())
            mins[2]=min(mins[2],seen_rows)
            cases+=1
    assert mins==[34,7,5]
    return cases


def type_check():
    # For every partition, some batch tests two surviving special primes.
    counts=(12,4,6,5)
    lower=[]
    pair_cost={(5,7):35,(5,11):34,(7,11):49}
    for a in product(*(range(n+1) for n in counts)):
        if sum(a)!=13:
            continue
        for left in range(4):
            b=tuple(n-x-(j==left) for j,(n,x) in enumerate(zip(counts,a)))
            if min(b)<0:
                continue
            scores=[value for (r,s),value in pair_cost.items()
                    if any(row[(5,7,11).index(r)+1] and row[(5,7,11).index(s)+1]
                           for row in (a,b))]
            assert scores
            lower.append(max(scores))
    assert min(lower)==34
    return len(lower)


if __name__=='__main__':
    print('Integer coverage and partial stages verified; cap and projections:',check_stage_and_scan())
    print('Arbitrary residual grid assignments:',exhaustive_grid())
    print('Batch type allocations with one outside row:',type_check())
