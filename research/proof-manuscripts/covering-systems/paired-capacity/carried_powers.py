"""Explicit paired covers allowing an earlier prime power to be certified and dropped."""
from math import gcd, lcm
from paired_digits import plan, powers, zero_budget


def construct(z, export=False, target=None):
    cap = z*(z+1)
    ps, choices = plan(z)
    stages = []
    skip = set()
    for p in ps[:-1]:
        if p in skip:
            continue
        segment = (p,)
        if p in choices:
            segment = (p,choices[p][0])
            skip.add(segment[1])
        stages.append(segment)

    tops = {p:max(powers(p,z+1)) for p in ps}
    eligible = {}
    for i,seg in enumerate(stages[:-1]):
        if len(seg)==1 and len(stages[i+1])==1:
            u = seg[0]
            following = stages[i+1][0]
            full = max(tops[u],max(powers(u,cap//max(following,u+1))))
            eligible[u] = [t for t in powers(u,full) if t>=tops[u]]
    if target is None:
        for u,values in eligible.items():
            tops[u] = values[-1]
    else:
        base = 1+sum((p-1)*len(list(powers(p,z+1))) for p in ps)
        base += sum((p-1)*(q-1) for p,(q,_) in choices.items())
        paths = {0:{}}
        for p,values in eligible.items():
            nxt = dict(paths)
            for weight,selection in paths.items():
                for j,t in enumerate(values[1:],1):
                    w = weight+j*(p-1)
                    if w <= target-base and w not in nxt:
                        nxt[w] = {**selection,p:t}
            paths=nxt
        tops.update(paths[target-base])
    old = virtual = 1
    actual = {}
    log = []
    def step(r, fixed, carried=None, final=False):
        nonlocal old, virtual
        if carried is None:
            carried = r*virtual
        packet = fixed if final else [*fixed,carried]
        projected = [gcd(old,n) for n in packet]
        assert len(packet)==r and lcm(*projected)==virtual
        for j,(n,g) in enumerate(zip(packet,projected)):
            assert g*r==n and virtual%g==0
            if not final and j==r-1:
                break
            assert 1<n<=cap and n not in actual
            actual[n] = (virtual*(j if final else j+1))%n
        if export:
            log.append({'r':r,'fixed':fixed,'carried':None if final else carried})
        old *= r
        virtual = carried

    pending, drop = 1,1
    for i,seg in enumerate(stages):
        p = seg[0]
        baseline = max(powers(p,z+1))
        if len(seg)==2:
            q,ds = choices[p]
            assert pending == 1
            step(p*q,[p*q*d for d in ds])
        else:
            ds = list(range(1,p))
            if pending>1:
                ds[-1] = pending
            step(p,[p*d for d in ds],carried=p*(virtual//drop))
        pending,drop = 1,1
        for u in seg:
            upper = tops[u]
            for v in list(powers(u, upper))[1:]:
                step(u,[v*d for d in range(1,u)])
            if upper>baseline and len(seg)==1:
                pending,drop=upper,upper//baseline
    assert pending == 1
    step(z,[z*d for d in [*range(1,z),z+1]],final=True)
    assert max(actual)==cap and lcm(*actual)==old
    assert target is None or len(actual)==target
    return actual,log


if __name__=='__main__':
    import argparse, json
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('z',type=int,nargs='*',default=[43,97,149,223,307,503])
    parser.add_argument('--export')
    args=parser.parse_args()
    for z in args.z:
        rows,log=construct(z,bool(args.export))
        cap=z*(z+1)
        upper=zero_budget(cap)
        print(f'z={z}, cap={cap}, k={len(rows)}, zero upper={upper}, difference={len(rows)-upper}')
        if args.export:
            assert len(args.z)==1
            with open(args.export,'w') as stream:
                json.dump({'z':z,'stages':log,'rows':rows},stream)
