"""Canonical divisor from a min cut; independent rank and contraction tests (Python 3)."""
from collections import deque
from functools import cache
from fractions import Fraction
from itertools import combinations, combinations_with_replacement
from math import gcd, isqrt, lcm, prod


def factor(n):
    f={}
    p=2
    while p*p<=n:
        while n%p==0:
            f[p]=f.get(p,0)+1
            n//=p
        p+=1
    if n>1:
        f[n]=1
    return f


def powers(n):
    return {p**j:p for p,e in factor(n).items() for j in range(1,e+1)}


def rank_profile(rows,budget):
    """Yield (threshold, unmatched count, largest maximizing divisor).

    Input supports may be pre-factored for large instances. Slots use capacities,
    not one vertex per copy. Distinct moduli >1 as in the research question.
    """
    rows=sorted(rows)
    assert len(set(rows))==len(rows) and all(n>1 for n in rows)
    digits=powers(lcm(*rows))
    slots={d:1+len(rows)+i for i,d in enumerate(digits)}
    sink=1+len(rows)+len(slots)
    graph=[{} for _ in range(sink+1)]
    def edge(i,j,c):
        graph[i][j]=c
        graph[j][i]=0
    for d,p in digits.items():
        edge(slots[d],sink,min(len(rows)+1,budget(p)))
    for i,n in enumerate(rows,1):
        edge(0,i,0)
        for d in powers(n):
            edge(i,slots[d],len(rows)+1)
    rank=0
    for i,n in enumerate(rows,1):
        graph[0][i]=1
        seen={0:None}
        queue=deque([0])
        while queue and sink not in seen:
            j=queue.popleft()
            for k,c in graph[j].items():
                if c and k not in seen:
                    seen[k]=j
                    queue.append(k)
        if sink in seen:
            rank+=1
            k=sink
            while k:
                j=seen[k]
                graph[j][k]-=1
                graph[k][j]+=1
                k=j
        # Complement of vertices reaching the sink = largest source min cut.
        reaches={sink}
        queue=deque([sink])
        while queue:
            j=queue.popleft()
            for k in graph[j]:
                if graph[k][j] and k not in reaches:
                    reaches.add(k)
                    queue.append(k)
        P=prod(digits[d] for d,node in slots.items() if node not in reaches)
        yield n,i-rank,P


def divisors(n):
    return [d for d in range(1,n+1) if n%d==0]


def test_profiles():
    total=0
    for N in (12,18,24,30,36,60):
        ds=divisors(N)[1:]
        for mask in range(1,1<<len(ds)):
            rows=[d for i,d in enumerate(ds) if mask>>i&1]
            T=lcm(*rows)
            for budget in (lambda p:p-1,lambda p:isqrt(p*(p-1)**2)):
                ts=divisors(T)
                cost={t:sum(budget(p) for p in powers(t).values()) for t in ts}
                prev=1
                last=0
                mass=Fraction(0)
                integral=Fraction(0)
                for i,(x,d,P) in enumerate(rank_profile(rows,budget)):
                    score={t:sum(t%n==0 and n<=x for n in rows)-c for t,c in cost.items()}
                    win=max(score.values())
                    assert d==win and P==lcm(*(t for t in ts if score[t]==win)) and P%prev==0
                    assert P%x==0 or d==last
                    if d>last:
                        mass+=Fraction(1,x)
                    integral+=d*(Fraction(1,x)-(Fraction(1,rows[i+1]) if i+1<len(rows) else 0))
                    prev,last=P,d
                    total+=1
                assert mass==integral
    return total


@cache
def cover(rows):
    if not rows:
        return False
    N=lcm(*rows)
    full=(1<<N)-1
    masks=[[sum(1<<x for x in range(a,N,n)) for a in range(n)] for n in rows]
    @cache
    def go(i,hit):
        if hit==full:
            return True
        if i==len(rows) or (full^hit).bit_count()>sum(N//n for n in rows[i:]):
            return False
        return any(go(i+1,hit|m) for m in masks[i])
    return go(1,masks[0][0])  # translate the first row to zero


@cache
def irreducible(rows):
    return cover(rows) and all(not cover(rows[:i]+rows[i+1:]) for i in range(len(rows)))


def test_contractions():
    trials=0
    positives=0
    for p in (2,3):
        others=[n for n in divisors(12) if n not in (1,p)]
        for length in range(7):
            for rest in combinations_with_replacement(others,length):
                rows=tuple(sorted((p,)*(p-1)+rest))
                residual=tuple(sorted(n//gcd(p,n) for n in rest))
                assert cover(rows)==cover(residual)
                actual=irreducible(rows)
                assert actual==(irreducible(residual) and any(n%p==0 for n in rest))
                trials+=1
                positives+=actual
    return trials,positives


def test_closure():
    trials=0
    for N in (24,30,36,60):
        ds=divisors(N)
        for mask in range(1,1<<(len(ds)-1)):
            rows=[d for i,d in enumerate(ds[1:]) if mask>>i&1]
            tops={}
            @cache
            def terminal(P,T):
                nexts=[p*P for p in factor(T//P)
                       if sum((P*p)%n==0 and P%n!=0 for n in rows)>=p-1]
                if not nexts:
                    return {P}
                return set.union(*(terminal(C,T) for C in nexts))
            for T in ds:
                finals=terminal(1,T)
                assert len(finals)==1
                tops[T]=next(iter(finals))
                assert all(tops[T]%tops[U]==0 for U in tops if T%U==0)
                trials+=1
    return trials


if __name__=='__main__':
    print('Exact flow/divisor profile comparisons:',test_profiles())
    print('Closure/order comparisons:',test_closure())
    print('Complete indexed quotient tests (total, irreducible):',test_contractions())
