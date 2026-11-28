"""Verify a positive linear combination of actual modular midpoint inequalities.

The symbols below are H evaluated at torus grid points. The final coefficient
vector has support three. All constraint multipliers and bounds are rational.
"""
from collections import defaultdict
from fractions import Fraction as F

def verify(E):
    q = 2*E
    e = q//E
    s0, stop = 19*q//16, 6*q//5
    h = 5
    m = (stop-s0)//(2*h)
    coeff = defaultdict(F)
    lower = F(0)
    count = 0

    def point(s,t,top=True):
        a = t + (q//2 if top else 0)
        return (a,s-a)

    def validate(p):
        a,b = p
        assert 0 <= a < q and 0 <= b < q
        assert 6*(a+b) >= 7*q+6*e and 12*(a+b) <= 17*q
        assert ((2*a>=q and 2*b<q) or
                (2*a<q and 2*b>=q and 2*(2*a+b)>=3*q+2*e))

    def add(x,y,z,w):
        nonlocal lower,count
        assert w >= 0
        for p in (x,y,z): validate(p)
        assert all((a+c-2*b)%q == 0 for a,b,c in zip(x,y,z))
        coeff[x] += w
        coeff[y] -= 2*w
        coeff[z] += w
        lower += w*F(sum((a-c)**2 for a,c in zip(x,z)),q*q)
        count += 1

    def interp(s,L,T,k,w):
        # Discrete Green kernel for the chord gap at k.
        for i in range(L+1,T):
            g = F((min(k,i)-L)*(T-max(k,i)),T-L)
            add(point(s,i-1),point(s,i),point(s,i+1),w*g)

    def P_minus_B(s,w):
        L = s-q+e
        T = q//2-e
        W = L+q//4
        lam = F(W-L,T-L)
        interp(s,L,T,W,w/lam)
        # Gives H(top W)-H(top L) >= 1/4 after identifying the two lifts.
        add(point(s,W),point(s,L),point(s,W,False),w/(2*lam))
        add(point(s,W),point(s,W,False),point(s,W),w/(4*lam))

    def P_minus_U(s,w):
        L = s-q+e
        T = q//2-e
        U = 3*q//2+2*e-s
        interp(s,L,T,U,w)
        P_minus_B(s,w*F(T-U,T-L))

    T = q//2-e
    for j in range(1,2*m):
        weight = min(j,2*m-j)
        s = s0+j*h
        Lminus = (s-h)-q+e
        Uplus = 3*q//2+2*e-(s+h)
        P_minus_B(s-h,F(weight))
        P_minus_U(s+h,F(weight))
        # Transfer the low-sheet value at U to the high sheet and the
        # midpoint at T in the opposite direction. Both identifications
        # are licensed by triples with equal endpoints.
        add(point(s-h,Lminus),point(s,T,False),point(s+h,Uplus,False),F(weight))
        add(point(s+h,Uplus),point(s+h,Uplus,False),point(s+h,Uplus),F(weight,2))
        add(point(s,T,False),point(s,T),point(s,T,False),F(weight))
    left = {p:w for p,w in coeff.items() if w}
    expected = {point(s0,T):1, point(s0+m*h,T):-2, point(s0+2*m*h,T):1}
    assert left == expected
    assert lower >= F(m*m,4)
    return m,count,len(coeff),float(lower),float(lower/2)

if __name__ == '__main__':
    print("inverse epsilon, half steps, weighted triples, grid symbols, certified second difference, certified oscillation")
    for E in (800,1600,3200):
        print(E,*verify(E),sep=", ")
