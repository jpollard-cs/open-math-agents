"""Independent finite matching and counting checks for the fixed-hub-prime problem."""
from collections import Counter
from math import isqrt, log, prod
from examples import matching

def split(n, H):
    t=1
    for h in H:
        while n%h==0:
            t*=h
            n//=h
    return t,n

def local_test():
    cases=0
    for H in [(),(2,),(3,),(2,3),(2,5)]:
        for p in [5,7,11]:
            if p in H: continue
            for N in range(1,110):
                groups=Counter(split(m,H)[0] for m in range(1,N+1))
                cap=sum(min(p*s,count) for s,count in groups.items())
                quotas=sorted(p*s for s in groups)
                assert matching([p*m for m in range(1,N+1)],quotas)==cap
                # Dual certificate: all small labels, and all rows of the other types.
                cut=max((s for s,c in groups.items() if p*s<=c),default=0)
                dual=sum(p*s if s<=cut else c for s,c in groups.items())
                assert dual==cap
                cases+=1
    print(f'{cases} finite placement optima verified against maximum matching and the exact cut.')

def largest_sieve(N):
    largest=[0]*(N+1)
    for p in range(2,N+1):
        if largest[p]==0:
            for m in range(p,N+1,p):
                largest[m]=p
    return largest

def direct_count(X,H):
    largest=largest_sieve(X)
    capacity=Counter()
    for n in range(2,X+1):
        hpart,rest=split(n,H)
        p=largest[rest] if rest>1 else 0
        if p<=12 or p*p>X or (rest//p)%p==0: continue
        capacity[hpart*p]+=1
    return sum(min(b,c) for b,c in capacity.items())

def second_count(X,H):
    # List possible cofactors per p, rejecting a prime as large as p in the cofactor.
    largest=largest_sieve(X//13+15)
    labels={}
    for p in range(13,isqrt(X)+1):
        if p in H or largest[p]!=p:continue
        for q in range(1,X//p+1):
            t,e=split(q,H)
            if e>1 and largest[e]>=p:continue
            b=t*p
            labels[b]=min(b,labels.get(b,0)+1)
    return sum(labels.values())

if __name__=='__main__':
    local_test()
    for H in [(),(2,),(2,3)]:
        v=prod(1-1/h for h in H)
        C=1-log(v)+2*sum(log(h)/(h-1) for h in H)
        for X in [10_000,50_000,250_000]:
            exact=direct_count(X,H)
            assert exact==second_count(X,H)
            print(f'H={H}, cap {X}, construction before fixed cover {exact}, normalized {exact*log(X)/X:.4f}, limit {C:.4f}')
