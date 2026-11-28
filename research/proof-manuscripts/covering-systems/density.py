"""Exact maximum-density residue classes on a finite divisibility chain and q times that chain."""
from math import gcd
from fractions import Fraction


def maximize(chain,q,pure,mixed):
    """All indices refer to chain with chain[0]=1. Return density and residues."""
    if not chain or chain[0]!=1 or q<2 or gcd(chain[-1],q)!=1:
        raise ValueError("invalid period")
    if any(y<=x or y%x for x,y in zip(chain,chain[1:])):
        raise ValueError("chain must be strictly increasing by divisibility")
    pure=sorted(pure)
    mixed=sorted(mixed)
    if any(i<1 or i>=len(chain) for i in pure) or any(i<0 or i>=len(chain) for i in mixed):
        raise ValueError("invalid index")
    if len(set(pure))!=len(pure) or len(set(mixed))!=len(mixed):
        raise ValueError("duplicate index")
    H=chain[-1]
    def residue_for_block(left,i):
        width=H//chain[i]
        assert left%width==0
        address=left//width
        residue=0
        for j in range(i,0,-1):
            radix=chain[j]//chain[j-1]
            digit=address%radix
            address//=radix
            residue+=digit*chain[j-1]
        return residue
    result={}
    left=0
    for i in pure:
        result[chain[i]]=residue_for_block(left,i)
        left+=H//chain[i]
    # Only active rows are stored, including when q is very large.
    ends={}
    for rank,i in enumerate(mixed):
        row=min(rank,q-1)
        end=ends.get(row,H)-H//chain[i]
        assert end>=0
        r=residue_for_block(end,i)
        n=chain[i]
        result[q*n]=r+n*((row-r)*pow(n,-1,q)%q)
        ends[row]=end
    total=q*left+sum(min(H-left,H-end) for end in ends.values())
    return Fraction(total,H*q),result
