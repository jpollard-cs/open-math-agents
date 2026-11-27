"""Construct distributions for a supplied finite mixture of permutations of equal cells."""
from math import log
from construct import construct, verify


def cell_constructor(k, mixture):
    """Entries are (positive integer weight, permutation of 0..h-1).
    The deterministic choice at each prime bounds total squared deviation
    by the sum of row variances, as in the distribution theorem.
    """
    if not mixture:
        raise ValueError("the mixture must have an entry")
    h = len(mixture[0][1])
    if not h or any(not isinstance(w,int) or w < 1 or sorted(s) != list(range(h))
                    for w,s in mixture):
        raise ValueError("positive integer weights and permutations of equal length are required")
    weight = sum(w for w,_ in mixture)
    error = [0] * (h+1)

    def choose_row(prefix, p, q, smallest):
        rows = []
        for w, perm in mixture:
            ds = set()
            for i, image in enumerate(perm):
                width = min(q*q, max(0, h*p*p - i*q*q))
                left = image*q*q
                first = max(1, (left + h*p - 1)//(h*p))
                last = (left + width - 1)//(h*p)
                ds.update(d for d in range(first,last+1) if prefix % d == 0)
            if len(ds) > p-1:
                ds = set(sorted(ds)[:p-1])
            if len(ds) < p-1:
                ds.update(sorted(smallest - ds)[:p-1-len(ds)])
            assert len(ds) == p-1
            counts = [0] * (h+1)
            for d in ds:
                counts[min(h,h*p*d//(q*q))] += 1
            rows.append((w,ds,counts))
        expected = [sum(w*counts[j] for w,_,counts in rows) for j in range(h+1)]
        def residual(counts):
            return [e+weight*c-u for e,c,u in zip(error,counts,expected)]
        _,ds,counts = min(rows,key=lambda row:sum(e*e for e in residual(row[2])))
        error[:] = residual(counts)
        return ds

    return construct(k,bulk_rule=choose_row)


def demo():
    mixture = [(2,(1,2,0)), (1,(0,2,1))]
    h = len(mixture[0][1])
    def G(t):
        return t*(1-log(t)) if t else 0
    target = [0.0] * h
    for w,perm in mixture:
        for i,image in enumerate(perm):
            target[image] += w*(G((i+1)/h)-G(i/h))/sum(v for v,_ in mixture)
    print("target cell masses:", [round(x,6) for x in target])
    for k in (1000,10000,100000):
        classes,levels = cell_constructor(k,mixture)
        verify(classes,levels)
        X = max(classes)
        counts = [0] * h
        for n in classes:
            counts[min(h-1,h*n//X)] += 1
        print("size, maximum, cell masses:", k,X,[round(c/k,6) for c in counts])


if __name__ == "__main__":
    demo()
