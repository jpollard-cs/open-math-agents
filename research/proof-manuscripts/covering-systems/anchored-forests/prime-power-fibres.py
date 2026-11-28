"""Sharp coverage count for an almost-covering old factor extended by p^e q."""
from itertools import combinations, product

def counts(p, q, t, e):
    n = q-t
    if not (0 < t < min(p,q)):
        raise ValueError('the common budget must be below both radices')
    h = n
    out = [h]
    for _ in range(e):
        h = max(0, p*h-t*min(n,h)-t)
        out.append(h)
    return out

def build(p,q,t,e):
    # Integers are recorded in least-significant-digit order along the p tree.
    n = q-t
    holes = {(0,y) for y in range(n)}
    phases = []
    modulus = 1
    for h1 in counts(p,q,t,e)[1:]:
        if not holes:
            break
        x = max(range(modulus), key=lambda a:sum((a,y) in holes for y in range(n)))
        largest = sum((x,y) in holes for y in range(n))
        assert largest == min(n,len(holes))
        holes = {(s + j*modulus,y) for s,y in holes for j in range(p)}
        stripes = [x+j*modulus for j in range(1,t+1)]
        holes = {(s,y) for s,y in holes if s not in stripes}
        cells = sorted(holes,key=lambda z:(z[0]==x,z))[:t]
        holes.difference_update(cells)
        phases.append((stripes,cells))
        assert len(holes)==h1
        modulus *= p
    return phases,holes

def brute(p,q,t,e):
    # Independent labelled search using exactly t distinct row and point
    # residues at every stage. Keep every possible mask on each small level.
    n=q-t
    masks={frozenset((0,y) for y in range(n))}
    period=1
    for _ in range(e):
        parents=masks; masks=set()
        for root in parents:
            children={(x+j*period,y) for x,y in root for j in range(p)}
            for stripes in combinations(range(period*p),t):
                left={v for v in children if v[0] not in stripes}
                for blocks in combinations(left,min(t,len(left))):
                    masks.add(frozenset(left.difference(blocks)))
        period*=p
    return min(map(len,masks))

def verify():
    tests=0
    for p,q,t,e in product(range(2,10),range(2,11),range(1,7),range(1,5)):
        if t>=min(p,q): continue
        n=q-t
        h=counts(p,q,t,e)[-1]
        alpha=p-t
        if n*(alpha-1)>=t:
            exact=p**e*n-(n+1)*t*((p**e-1)//(p-1))
        else:
            series=sum(alpha**j for j in range(e))
            exact=max(0,alpha**e*n-t*series)
        assert h==exact
        # Large boards are covered by the closed-form comparison.
        if p**e*q<2500: assert len(build(p,q,t,e)[1])==h
        tests+=1
    cases=[(p,q,t,1) for p in range(2,5) for q in range(2,6)
           for t in range(1,min(p,q))]
    cases += [(2,2,1,2),(2,3,1,2),(2,4,1,2),(3,2,1,2),(3,3,2,2),(2,3,1,3)]
    for p,q,t,e in cases: assert brute(p,q,t,e)==counts(p,q,t,e)[-1]
    print(tests,'closed-form checks;',len(cases),'independent exhaustive small cases')
    print('Candidate old sections:',[(q,counts(5,q,3,3)[-1]) for q in (7,13,17)])
    # A 35-hole cross for H=4, p=5, q=7, using three old dressings.
    core=[(1,2),(2,4)]
    def lift(d,z,m):
        return (d*(z*pow(d,-1,m)%m),d*m)
    core += [lift(d,y,7) for d,y in zip((1,2,4),(4,5,6))]
    for j in (1,2,3):
        f=5**j
        core += [lift(d,i*5**(j-1),f) for d,i in zip((1,2,4),(2,3,4))]
        for d,y in zip((1,2,4),(1,2,3)):
            z=next(z for z in range(7*f) if z%7==y and z%f==5**(j-1))
            core.append(lift(d,z,7*f))
    holes=[u for u in range(3500) if all(u%m!=a for a,m in core)]
    vs={(u%125,u%7) for u in holes}
    xs={u%125 for u in holes}
    assert len(core)==23 and len(set(m for a,m in core))==23
    assert len(holes)==35 and len(xs)==32 and vs==({(x,0) for x in xs}|{(0,y) for y in (1,2,3)})
    print('23 original old divisors verified on all 3500 residues; 32+3 cross.')
    return core,holes
if __name__=='__main__': verify()
