"""Sieve for examples of the three required primes and check the parity obstruction."""
from math import isqrt
from fractions import Fraction


def prime_table(bound):
    prime = bytearray([1])*(bound+1)
    prime[:2] = bytes([0,0])
    for d in range(2,isqrt(bound)+1):
        if prime[d]:
            prime[d*d::d] = bytes(1+(bound-d*d)//d)
    return prime


def run():
    limit = 300000
    prime = prime_table(3*limit)
    odd_partners = [p for p in range(3,limit,2) if prime[p]]
    count = 0
    for d in range(4,101):
        first = None
        for p in odd_partners:
            m = d*p
            if m > limit:
                break
            if p <= d:
                continue
            i,j = 3*m-2,3*m-1
            u = i if i % 2 else j
            v = (j if i % 2 else i)//2
            found = prime[u] and prime[v]
            if d % 2:
                from_forms = prime[3*d*p-2] and prime[(3*d*p-1)//2]
                if found:
                    assert p % 4 == d % 4
            else:
                from_forms = prime[3*d*p-1] and prime[(3*d*p-2)//2]
            assert found == from_forms
            if found:
                assert d % 4 != 2
                target = 3 * Fraction(3*d+1,3*d) / Fraction(d+1,d)
                assert target == 3 - Fraction(2,d+1)
                count += 1
                if first is None:
                    first = m
        if d <= 9:
            print(f"d={d}: first m in search = {first}")
    print(f"{count} prime-triple witnesses within the finite ranges passed.")
    print("Finite witnesses do not prove any infinitude assertion.")


if __name__ == "__main__":
    run()
