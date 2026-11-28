"""Produce covering residues, using saturation to reduce large periods first."""
from functools import cache
from math import lcm
import json
from pathlib import Path
from enumerate_covers import prime_powers, row_masks

@cache
def witness(moduli):
    if 1 in moduli:
        return tuple(0 for d in moduli)
    period=lcm(*moduli)
    if sum(period//d for d in moduli)<period:
        return None
    options=[]
    for p,power in prime_powers(period):
        top=[i for i,d in enumerate(moduli) if d%power==0]
        options.append((len(top)-p,p,power,top))
    if not options:
        return None
    excess,p,power,top=min(options)
    if excess<=0:
        ordinary=[(d,i) for i,d in enumerate(moduli) if i not in top]
        if excess==0:
            joint=lcm(*(moduli[i]//p for i in top))
            ordinary.append((joint,-1))
        ordinary.sort()
        small=witness(tuple(d for d,_ in ordinary))
        if small is None:
            return None
        vals=[0]*len(moduli)
        for (_,idx),a in zip(ordinary,small):
            if idx>=0:
                vals[idx]=a
            else:
                for digit,i in enumerate(top):
                    projection=moduli[i]//p
                    vals[i]=next(v for v in range(a%projection,moduli[i],projection)
                                 if v//(power//p)%p==digit)
        return tuple(vals)

    rows=[row_masks(period,d) for d in moduli]
    def recurse(i,holes):
        if holes==0:
            return (0,)*(len(rows)-i)
        if i==len(rows):
            return None
        cap=[max((holes&mask).bit_count() for mask in row) for row in rows[i:]]
        need=holes.bit_count()-sum(cap[1:])
        if need>cap[0]:
            return None
        residues=range(1) if i==0 else range(moduli[i])
        for a in sorted(residues,key=lambda a:-(rows[i][a]&holes).bit_count()):
            gain=holes&rows[i][a]
            if gain.bit_count()>=need and gain:
                rest=recurse(i+1,holes^gain)
                if rest is not None:
                    return (a, *rest)
        return None
    return recurse(0,(1<<period)-1)

def write_witnesses(rows):
    result={}
    for k in sorted({len(s) for s in rows if len(s)>=16}):
        s=min((s for s in rows if len(s)==k),key=lambda s:(s[-1],tuple(s)))
        a=witness(tuple(s))
        assert a is not None
        assert all(any((x-r)%d==0 for d,r in zip(s,a)) for x in range(lcm(*s)))
        result[k]=dict(moduli=s,residues=a)
    return result

if __name__=='__main__':
    import sys
    data=json.loads(Path(sys.argv[1]).read_text())
    print(json.dumps(write_witnesses(data),indent=2))
