"""Check every candidate-pool change relevant to sizes 26–30."""
from math import isqrt
from fixed_sizes import OLD,SEVEN

def eligible(n,cap):
    rem=n
    for p in range(2,isqrt(n)+1):
        if rem%p:continue
        power=1
        while rem%p==0:
            rem//=p;power*=p
        if power*(p+1)>cap:return False
    return rem==1 or rem*(rem+1)<=cap
prev=set()
for cap in range(47,97):
    vals={n for n in range(2,cap+1) if eligible(n,cap)}
    changes={47:OLD,48:(16,48),56:SEVEN,60:(60,),63:(63,),70:(70,),72:(72,),80:(80,),84:(84,),90:(90,),96:(32,96)}
    assert vals-prev==set(changes.get(cap,()))
    assert prev<=vals
    if vals!=prev:print(cap,sorted(vals-prev))
    prev=vals
