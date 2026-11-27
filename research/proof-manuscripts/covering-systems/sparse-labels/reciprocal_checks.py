"""Check the exact local weighted optimizer and capped geometric entropy by separate methods."""
from fractions import Fraction
from math import gcd,log,prod
from examples import matching
from hub_checks import split

def greedy_weight_checks():
    cases=0
    for H in [(),(2,),(3,),(2,3)]:
        for p in (5,7):
            limit=190
            parts={split(n,H)[0] for n in range(1,limit+1)}
            labels=sorted(p*s for s in parts)
            chosen=[]
            for m in range(1,limit+1):
                if matching(chosen+[p*m],labels)==len(chosen)+1: chosen.append(p*m)
            count={}
            exact=[]
            for m in range(1,limit+1):
                s=split(m,H)[0]
                if count.get(s,0)<p*s:
                    count[s]=count.get(s,0)+1
                    exact.append(p*m)
            assert chosen==exact
            assert sum(Fraction(1,n) for n in chosen)==sum(Fraction(1,n) for n in exact)
            cases+=1
    print('Exact greedy independence checks match the local harmonic optimizer in all',cases,'cases.')

def capped_gain(H,J):
    B=prod(h**J for h in H)
    counts={}
    for m in range(1,B+1):
        s=gcd(m,B);counts[s]=counts.get(s,0)+1
    exact=sum((c/B)*log(s*B/c) for s,c in counts.items())
    # Independent computation via the entropy and mean of each geometric variable.
    factor=0.
    for h in H:
        for j in range(J+1):
            w=(1-1/h)*h**(-j) if j<J else h**(-j)
            factor+=w*(j*log(h)-log(w))
    assert abs(factor-exact)<1e-10
    return exact
if __name__=='__main__':
    greedy_weight_checks()
    for H in [(2,),(3,),(2,3)]:
        lim=-sum(log(1-1/h) for h in H)+2*sum(log(h)/(h-1) for h in H)
        vals=[capped_gain(H,j) for j in range(1,7)]
        assert all(x<y for x,y in zip(vals,vals[1:])) and vals[-1]<lim
        print('H',H,'capped second-order gains',*(round(x,5) for x in vals),'limit',round(lim,5))
