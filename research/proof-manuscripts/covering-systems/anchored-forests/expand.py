"""Generate Sun one-hole cores, with the one- and two-prime completions."""
from math import isqrt


def extra(maximum, primes):
    covers = []

    def visit(core, divisor_count, last_prime):
        for p in primes:
            if p <= last_prime:
                continue
            if core * p > maximum:
                break
            if p <= divisor_count:
                covers.append(core * p)
                continue
            if p == divisor_count + 1:
                extension = core * p
                exponent = 1
                while extension <= maximum:
                    visit(extension, divisor_count * (exponent + 1), p)
                    extension *= p
                    exponent += 1
                continue
            if p - divisor_count > isqrt(divisor_count):
                break
            for q in primes:
                if q <= p:
                    continue
                if core * p * q > maximum or (p - divisor_count) * (q - divisor_count) > divisor_count:
                    break
                covers.append(core * p * q)

    visit(1, 1, 1)
    return covers
