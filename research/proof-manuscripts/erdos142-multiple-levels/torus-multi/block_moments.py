from fractions import Fraction as F
def polygon(x0,x1,y0,y1,halfspaces):
    p=[(x0,y0),(x1,y0),(x1,y1),(x0,y1)]
    for a,b,c in halfspaces:
        n=[]
        for u,v in zip(p,p[1:]+p[:1]):
            f=a*u[0]+b*u[1]-c;g=a*v[0]+b*v[1]-c
            if f>=0:n.append(u)
            if (f>=0)!=(g>=0):n.append(tuple(A+(B-A)*f/(f-g) for A,B in zip(u,v)))
        p=n
    return p
def moments(p):
    area=m=F(0)
    for a,b in zip(p,p[1:]+p[:1]):
        det=a[0]*b[1]-b[0]*a[1];u=sum(a);v=sum(b)
        area+=det/2;m+=det*(u*u+u*v+v*v)/12
    return area,m
def polygons():
    L=F(2,3);U=F(7,6);T=F(17,12); h=F(1,2); Z=F(0);E=F(1)
    return [polygon(h,E,Z,E,[(1,1,L),(-1,-1,-U)]),
            polygon(h,E,Z,h,[(1,1,U),(-1,-1,-T)]),
            polygon(Z,h,h,E,[(1,1,U),(-1,-1,-T),(2,1,F(3,2))])]
if __name__=='__main__':
    stats=list(map(moments,polygons()));a=sum(x for x,y in stats);m=sum(y for x,y in stats)
    print(stats,a,m,m/a,float(m/a),float(m/a)**0.5)
