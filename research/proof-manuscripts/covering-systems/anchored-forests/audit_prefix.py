"""Exact arithmetic for the prime-prefix test in the covering-number census."""
from functools import cache
from math import comb, prod
from itertools import combinations
from collections import Counter
@cache
def bell_coefficients(t, degree):
    values=[1]
    for j in range(degree):
        values.append(-t*sum(comb(j,i)*values[i] for i in range(j+1)))
    return values

def numerator(t, factors):
    # The coefficient of z^i encodes choosing i axes for a coprime partition.
    coeff=[1]
    for p,a in factors:
        denominator=p**a
        numerator=(denominator-1)//(p-1)
        coeff=[v*denominator+w*numerator for v,w in zip(coeff+[0],[0]+coeff)]
    return sum(x*y for x,y in zip(coeff,bell_coefficients(t,len(factors))))

def sun_split(factors):
    t=1
    for i,(p,a) in enumerate(factors):
        if p<=t:return 0,()
        if p!=t+1:return t,factors[i:]
        t*=a+1
    return t,()

def audit(limit):
    spf=list(range(limit+1))
    for i in range(2,int(limit**.5)+1):
        if spf[i]!=i:continue
        for j in range(i*i,limit+1,i):
            if spf[j]==j:spf[j]=i
    counts=Counter()
    examples=[]
    for n in range(1,limit+1):
        a=n; f=[]
        while a>1:
            p=spf[a];e=0
            while a%p==0:a//=p;e+=1
            f.append((p,e))
        t,tail=sun_split(f)
        if not t:counts['automatic']+=1;continue
        if not tail:counts['core_only']+=1;continue
        if numerator(t,tail)<=0:counts['vacuous']+=1;continue
        # Positivity on all proper prime-power prefixes is sufficient.
        if all(numerator(t,tail[:j])>0 for j in range(1,len(tail))):
            counts['certified']+=1
        else:
            counts['flagged']+=1
            if len(examples)<10:examples.append((n,t,tail))
    return counts,examples
if __name__=='__main__':
    print(audit(10**6),flush=True)
