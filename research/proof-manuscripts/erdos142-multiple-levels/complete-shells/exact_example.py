"""Exact branch and bound for complete layers at q=3, d=12."""
from itertools import combinations_with_replacement
from collections import Counter

def instance(q,d):
    singles=[(a*a,((a+c)//2)**2,c*c) for a in range(q+1) for c in range(q+1) if not (a+c)%2]
    states={(0,0,0)}
    weights=Counter({0:1})
    for _ in range(d):
        states={(x+a,y+b,z+c) for x,y,z in states for a,b,c in singles}
        out=Counter()
        for s,w in weights.items():
            for v in range(q+1):out[s+v*v]+=w
        weights=out
    # Cross-check the support by enumerating multisets of coordinate triples.
    other=set()
    for pattern in combinations_with_replacement(singles,d):
        other.add(tuple(map(sum,zip(*pattern))))
    assert states==other
    return weights,{tuple(sorted({x,y,z})) for x,y,z in states if x!=y or z!=y}

def optimize(weights,forbidden):
    radii=sorted(weights,key=lambda v:(-weights[v],v))
    ids={v:i for i,v in enumerate(radii)}
    k=len(radii)
    pair=[0]*k
    third=[[0]*k for _ in range(k)]
    for edge in forbidden:
        members=[ids[v] for v in edge]
        if len(members)==2:
            a,b=members;pair[a]|=1<<b;pair[b]|=1<<a
        else:
            a,b,c=members
            for u,v,w in ((a,b,c),(a,c,b),(b,c,a)):
                third[u][v]|=1<<w;third[v][u]|=1<<w
    val=[weights[v] for v in radii]
    best=0;chosen=();nodes=0
    def ub(mask):
        # Partition candidates into pair-conflict cliques. The first vertex
        # of each clique is its heaviest, so its weight bounds its contribution.
        ans=0
        while mask:
            clique=mask
            ans+=val[(clique&-clique).bit_length()-1]
            while clique:
                bit=clique&-clique;i=bit.bit_length()-1
                mask^=bit
                clique=(clique^bit)&pair[i]
        return ans
    def dfs(mask,prior,total):
        nonlocal best,chosen,nodes
        nodes+=1
        if total>best:
            best=total;chosen=prior
        if total+ub(mask)<=best:return
        bit=mask&-mask;i=bit.bit_length()-1;rest=mask^bit
        forbidden_now=pair[i]
        for v in prior:forbidden_now |=third[v][i]
        dfs(rest&~forbidden_now,prior+(i,),total+val[i])
        dfs(rest,prior,total)
    dfs((1<<k)-1,(),0)
    result=sorted(radii[i] for i in chosen)
    assert all(not set(e).issubset(result) for e in forbidden)
    return best,result,nodes

if __name__=='__main__':
    w,h=instance(3,12);best,r,n=optimize(w,h)
    print('Exact maximum:',best)
    print('Squared radii:',*r)
    print('Forbidden two- and three-radius sets:',sum(len(e)==2 for e in h),sum(len(e)==3 for e in h))
    print('Search nodes:',n)
