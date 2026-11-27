"""Exact quadrature bounds for the EGIP exponent-pair block majorants."""
from fractions import Fraction as Q
from itertools import combinations

c = Q(4, 9)
b = 1 - c + Q(1, 10000)
pairs = dict(B=(Q(1,2),Q(1,2)), AB=(Q(1,6),Q(2,3)), AAB=(Q(1,14),Q(11,14)))


def theta(pair, u, window=c):
    k, l = pair
    den = window*(1+k)-k+(k-l)*u
    assert den > 0 and l >= k
    return 2*(1+k-l)/den


def rectangles(names, window, right, blocks=256):
    points = [window + j*(right-window)/blocks for j in range(blocks+1)]
    # Each majorant and their lower envelope are positive nondecreasing here.
    values = [u*min(theta(pairs[name],u,window) for name in names) for u in points]
    step = (right-window)/blocks
    return window+sum(values[:-1])*step, window+sum(values[1:])*step


for size in (2,3):
    for names in combinations(pairs,size):
        lower,upper=rectangles(names,c,b)
        print(names,'enclosure in millionths',int(lower*10**6),int(upper*10**6)+1)
        if size == 2:
            thresholds = {('B','AB'):1002460, ('B','AAB'):1026483, ('AB','AAB'):1000172}
            assert lower > Q(thresholds[names],10**6)
        else:
            assert upper < Q(994572,10**6)

edges=[c]
for right in (Q(77,162),Q(29,54),b):
    start=edges[-1]
    edges.extend(start+(right-start)*i/16 for i in range(1,17))
for j,omit in [(0,'AAB'),(24,'AB'),(47,'B')]:
    u,v=edges[j:j+2]
    gap=(v-u)*(min(theta(p,u) for name,p in pairs.items() if name!=omit)-theta(pairs[omit],v))-Q(1,10**6)
    expected = {0:Q(67154761,32739000000), 24:Q(43743223,6777000000), 47:Q(157845367,96689250000)}
    assert gap == expected[j] and gap > 0
    print('H1 band',j,'allowance exceeded by at least',gap)
