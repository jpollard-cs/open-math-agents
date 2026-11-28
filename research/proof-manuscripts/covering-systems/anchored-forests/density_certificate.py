"""Exact union of multiples, verified by both valuation conditioning and inclusion-exclusion."""
from population import read_table,reduce_set,uncovered
from math import gcd,prod
from functools import cache
from fractions import Fraction
from expand import extra
from pathlib import Path
@cache
def ie(items):
    if not items:return Fraction(1)
    if items[0]==1:return Fraction(0)
    t=items[-1];other=items[:-1]
    quotients=reduce_set(d//gcd(t,d) for d in other)
    return ie(other)-ie(quotients)/t
if __name__=='__main__':
    primes=[2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53]
    N=773500
    lifts=[5,13,19,23,29,31,37*41,37*43]
    table=read_table()
    assert len(table)==94 and reduce_set(table)==tuple(table)
    assert reduce_set(b//gcd(b,N) for b in table)==(2,3,7,11)
    known=extra(10**10,primes)
    for family in [table,table+[N*k for k in lifts],table+known,table+known+[N*k for k in lifts]]:
        minimal=reduce_set(family)
        d=1-uncovered(minimal)
        independent=1-ie(minimal)
        assert d==independent
        print(len(minimal),d,float(d),flush=True)
