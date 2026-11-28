"""Exact small examples of the smooth envelope and the first prime thresholds."""
from fractions import Fraction
from itertools import count, islice
from check_period import best,primes

def smooth_numbers(ps):
    for n in count(2):
        m=n
        for p in ps:
            while m%p==0:m//=p
            if m==1:
                yield n
                break

def one(k):
    all_primes=primes(k)
    budget=0; smooth_primes=[]
    for p in all_primes:
        if budget+p-1>k-1:break
        budget+=p-1;smooth_primes.append(p)
    V=sum(Fraction(1,n) for n in islice(smooth_numbers(smooth_primes),k))
    U,exp,ds=best(k,True)
    assert U>0 and V>=U
    q=smooth_primes[-1]
    last=[max((p for p,a in zip(all_primes,exp) if a>=j),default=0) for j in (1,2,3,4)]
    print(k,q,*last,f"{float(V-U):.8f}",f"{float(V-U)*q**(2/3):.6f}",flush=True)

if __name__=='__main__':
    print('k q largest-prime squared-through cubed-through fourth-through   V-U   q^(2/3)(V-U)')
    for k in (10,20,30,40,50,60,70,80,90,100):one(k)
