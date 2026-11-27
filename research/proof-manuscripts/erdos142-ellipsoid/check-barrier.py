"""Exact rational validation of the family that attains the curvature limit."""
from fractions import Fraction as F

def high(a, b, e):
    return (F(7,6)+e <= a+b <= F(17,12) and
            ((F(1,2)<=a<1 and 0<=b<F(1,2)) or
             (0<=a<F(1,2)<=b<1 and 2*a+b>=F(3,2)+e)))

def g(a):
    return (a if a<F(1,2) else a-F(1,2))**2

def critical_scaled(E, beta):
    e = F(1,E)
    x = F(3,4)-2*e, F(1,2)-e**2
    z = F(1,4)+2*e-e**2, 1-3*e+2*e**2
    y = tuple((a+b)/2 for a,b in zip(x,z))
    assert all(high(*p,e) for p in [x,y,z])
    lhs = sum((a-b)**2 for a,b in zip(x,z))-beta*(g(x[0])+g(z[0])-2*g(y[0]))
    gap = sum(x)**2+sum(z)**2-2*sum(y)**2
    assert gap == (e+2*e**2)**2/2
    return e**2*lhs/gap
if __name__ == "__main__":
    print("beta, inverse epsilon, scaled lower witness, limit")
    for beta in (F(9,2), F(6), F(10)):
        for E in (100,1000,10000,100000):
            value = critical_scaled(E,beta)
            limit = 1+3*beta/4
            assert abs(value-limit)<(20*beta+40)/E
            print(beta, E, f"{float(value):.7f}", limit, sep=", ")
