"""All exact zero-defect sizes 6284--6334 at their minimum cap, with witnesses."""
from math import gcd,lcm
from paired_digits import primes,powers,zero_budget

Z = 257
CAP = 66563
PS = [p for p in primes(Z) if p != 131]
BASE = {p:max(powers(p,Z+1)) for p in PS}


def options():
    paths = {0:{}}
    for p,q in zip(PS[:-2],PS[1:-1]):
        extra = 0
        for t in powers(p,CAP//max(q,p+1)):
            if t > BASE[p]:
                extra += 1
        nxt = dict(paths)
        for total,choices in paths.items():
            for count in range(1,extra+1):
                newtotal = total + count*(p-1)
                if newtotal not in nxt:
                    nxt[newtotal] = {**choices,p:count}
        paths=nxt
    return paths


def build(k):
    plain = 1+sum((p-1)*len(list(powers(p,BASE[p]))) for p in PS)
    opt = options()[k-plain]
    old=carry=1
    stages=[]
    allrows={}
    anchor=drop=1
    def record(radix, fixed, virtual=None):
        nonlocal old,carry
        packet=fixed if virtual is None else [virtual,*fixed]
        proj=[gcd(n,old) for n in packet]
        assert len(packet)==radix and all(n==radix*g for n,g in zip(packet,proj))
        assert lcm(*proj)==carry
        for j,n in enumerate(fixed):
            assert n not in allrows and 1<n<=CAP
            allrows[n]=(carry*(j if virtual is None else j+1)) % n
        stages.append({'fixed':fixed,'carried':virtual})
        old *= radix
        carry = virtual
    for p in PS[:-1]:
        cofs=[d for d in range(1,p) if d!=131]
        if len(cofs)<p-1:
            cofs.append(p+1)
        if anchor>1:
            cofs[-1]=anchor
        record(p,[p*d for d in cofs],p*(carry//drop))
        anchor=drop=1
        top=BASE[p]*p**opt.get(p,0)
        for t in list(powers(p,top))[1:]:
            record(p,[t*d for d in cofs_without_anchor(p)],p*carry)
        if top>BASE[p]:
            anchor,drop=top,top//BASE[p]
    assert anchor==1
    ds=[d for d in range(1,257) if d!=131]+[258,259]
    record(Z,[Z*d for d in ds])
    assert len(allrows)==k and max(allrows)==CAP and lcm(*allrows)==old
    assert 1+sum((p-1)*(len(list(powers(p,BASE[p])))+opt.get(p,0)) for p in PS)==k
    return allrows,stages


def cofs_without_anchor(p):
    return [d for d in range(1,p) if d!=131]+([p+1] if p>131 else [])


if __name__=='__main__':
    for k in range(6284,6335):
        build(k)
    from carried_powers import construct
    for k in range(6284,6314):
        construct(251,target=k)
    print("30 positive-defect covers, sizes 6284..6313, cap 63252.")
    small=[*range(1,257),258]
    forced=lcm(Z,*small)
    minsize=1+sum(p-1 for p in primes(Z) for t in powers(p,Z+1) if forced%t==0)
    assert minsize==6335 and zero_budget(CAP-1)-256==6283
    print('51 independent packet lists verified, sizes 6284..6334, cap 66563.')
    print('Through cap 66562: zero budget without 257 = 6283; with 257 forced size >=6335.')
