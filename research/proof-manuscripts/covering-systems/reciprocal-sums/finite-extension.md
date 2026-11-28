# Exact minimum largest moduli for sizes 16 through 23

Codex, at the request of Jordan Pollard · 27 November 2026 · computational result for review

Let m(k) be the minimum possible largest modulus among irreducible covering sets with exactly k distinct moduli greater than one. Irreducibility means that after dropping any member, coverage is impossible even with a completely fresh choice of residues.

| k | 16 | 17 | 18 | 19 | 20 | 21 | 22 | 23 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| m(k) | 48 | 56 | 56 | 56 | 56 | 56 | 56 | 56 |

The [earlier table and proof](./erdos1189-reciprocal-sums-and-exact-minima.pdf) cover k from 5 through 15. The [witness file](./witnesses-through-23.json) gives concrete modulus–residue pairs at each new minimum. Every witness covers its full period. The exclusion of smaller maxima and of all proper subsets comes from the exhaustive searches described below.

## Why the number of cases is finite

If p^a is the full power of p in the period L, at least p distinct moduli are divisible by p^a. Their cofactors are coprime to p, so (p+1)p^a is at most the largest modulus. This is proved by the private-point fibre argument on page 5 of the companion paper.

At cap 55 the period therefore divides 720 and there are 19 candidate moduli. The search finds 1,444 irreducible sets. None has more than 16 members. Exactly one has 16, and its maximum is 48. At cap 47 the two algorithms return the identical 741 sets, and all have size at most 15.

At cap 56 the period divides 5,040. Seven enters as a prime factor. The moduli prime to 7 are exactly the same 19 candidates as at cap 55. A set actually involving 7 must use all seven possible multiples: 7, 14, 21, 28, 35, 42 and 56. Their projected cofactors have least common multiple 120. Thus the seven classes can be replaced by one class modulo 120 when testing coverage, by the saturation argument on page 5 of the companion. Conversely any covering with modulus 120 lifts to those seven moduli. After deleting a 7-multiple, one section stays empty of 7-multiples, so the remaining ordinary moduli alone would have to cover. After deleting an ordinary class the same contraction still applies. Consequently irreducibility of the expanded set is equivalent to irreducibility of the contracted set as a list. The modulus 120 is distinct from all ordinary candidates. The calculation yields 2,912 expansions, hence 4,356 irreducible sets in total at cap 56. Sizes 17 through 23 all occur.

## Five-section decision method

For the nontrivial searches modulo 5, the period is 5B with 5 coprime to B. Classes with moduli prime to 5 give the same covered base set in each of the five sections. If they already cover, return true. Otherwise translate a base hole to 0. Each remaining modulus 5d is placed in one section and projects to a residue class modulo d in the base. Every section must receive a class. Permuting the five section labels does not affect feasibility, so enumerate all partitions of the labelled cofactors into five nonempty groups.

In each singleton group the unique base class must contain 0. Intersecting these classes restricts the possible common holes to 0 modulo the LCM of their cofactors. In a larger group enumerate all ways to cover points of this support by the union of one class per cofactor, keeping unions containing 0. A choice disjoint from the support can always be replaced by a class through 0, which only enlarges the supported union. Intersect the allowed sets from all groups. The ordinary moduli must cover the complement of this intersection; require their residues to avoid 0. These conditions are necessary by translation. They are sufficient because one can place the indicated projected classes in their assigned sections using the Chinese remainder theorem. In every union/intersection step, a contained allowed set may be discarded in favor of a superset. Remaining ordinary choices are tested by exact bit-set search with an upper bound on the number of points still coverable.

## Reproduction

Use the Python standard library. From this directory run:

```sh
python section_solver.py 47
python section_solver.py 55
python at56.py
python witnesses.py full-56.json > rebuilt-witnesses.json
```

The size-47 result is directly comparable to the original complete catalog. The alternate program `python enumerate_covers.py 55` uses the original decision method without the five-section optimization. The final witness script independently reconstructs displayed congruences and exhausts each resulting period. These arithmetic searches establish finite values of m(k); a formula for arbitrary k remains open in this work.
