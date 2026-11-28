"""Exact finite relaxation, compression cross-check and forbidden-cover certificates."""
from fractions import Fraction
from functools import reduce
from heapq import merge
from itertools import islice
from math import isqrt, lcm, prod, log
import json
from pathlib import Path

def primes(k):
    return [p for p in range(2,k+1) if all(p%d for d in range(2,isqrt(p)+1))]

def best(k,compressed):
    ps=primes(k)
    record=(Fraction(0),(),())
    def assess(exps):
        nonlocal record
        if prod(a+1 for a in exps)<k+1: return
        ds=[1]
        for p,a in zip(ps,exps):
            scaled=[[d*p**j for d in ds] for j in range(a+1)]
            ds=list(islice(merge(*scaled),k+1))
        value=sum((Fraction(1,d) for d in ds[1:]),Fraction())
        if value>record[0]: record=value,tuple(exps),tuple(ds[1:])
    def search(i,budget,exp,prev):
        if i==len(ps) or ps[i]-1>budget:
            assess(exp);return
        p=ps[i]
        largest=budget//(p-1)
        if compressed:largest=min(largest,prev)
        for a in range(largest+1):
            if compressed and not a:
                assess(exp);continue
            search(i+1,budget-a*(p-1),exp+[a],a)
    search(0,k-1,[],k)
    return record

def check_forbidden():
    cert=json.loads(Path("forbidden-covers.json").read_text())
    values=sorted(set().union(*(c["moduli"] for c in cert)))
    scale=lcm(*values)
    for c in cert:
        ds,rs=c["moduli"],c["residues"]
        assert len(set(ds))==len(ds)==len(rs)
        assert all(0<=r<d for r,d in zip(rs,ds))
        assert all(any(x%d==r for r,d in zip(rs,ds)) for x in range(lcm(*ds)))
    masks=[sum(1<<values.index(d) for d in c["moduli"]) for c in cert]
    weights=[scale//d for d in values]
    sums=[0]*(1<<len(values))
    bestcost=scale*100
    for m in range(1,len(sums)):
        bit=m & -m
        sums[m]=sums[m^bit]+weights[bit.bit_length()-1]
        if sums[m]<bestcost and all(m&b for b in masks):bestcost=sums[m]
    assert Fraction(bestcost,scale)==Fraction(7,30)
    print(len(cert),"exact covering assignments and",len(sums),"omission sets verified; minimum mass 7/30.")

if __name__=="__main__":
    check_forbidden()
    for k in range(2,19):
        assert best(k,False)[0]==best(k,True)[0]
    print("Unrestricted and compressed period searches agree on feasibility and optimum at k=2 through 18.")
    for k in (10,20,30,40,50):
        score,exps,ds=best(k,True)
        print("k =",k,"optimal exponents =",exps,"maximum divisor =",ds[-1],"reciprocal sum =",score)
