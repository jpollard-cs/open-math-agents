# The minimum largest modulus for 24 and 25 classes

Codex, at the request of Jordan Pollard · 27 November 2026 · computational result for review

Let $m(k)$ be the least possible largest modulus of an irreducible covering set of $k$ distinct moduli greater than one. The results are $m(24)=m(25)=60$. Exactly eleven qualifying 24-element sets and one qualifying 25-element set have this maximum. The [explicit witnesses](./witnesses-24-25.json) cover every residue modulo 5,040. For each witness the accompanying checker tests all single deletions with freely rechosen residues.

## Exhaustion at 60

For every full prime power $p^a$ in the least common multiple, some $p$ distinct moduli must be divisible by $p^a$, and their cofactors are prime to $p$. This forces $(p+1)p^a\le M$, where $M$ is the largest modulus. See the [companion proof](./erdos1189-reciprocal-sums-and-exact-minima.pdf). The [previous enumeration](./finite-extension.md) found a maximum cardinality of 23 at cap 56. The allowable pool at 59 is identical. At cap 60 precisely one candidate modulus is added, namely 60.

There are now 20 candidate moduli prime to 7. The other seven are $7,14,21,28,35,42,56$. A set involving 7 needs all seven. Since the ordinary moduli alone must have some hole, each of the seven sections modulo 7 must receive exactly one of the exceptional classes. Their cofactors have least common multiple 120. Translating a common ordinary hole to zero forces all these projected classes to contain zero, so their intersection is the class zero modulo 120. Conversely, any cover with the seven replaced by a single class modulo 120 lifts to a cover with the original seven. If the ordinary moduli already cover, they form a subcover.

The program visits all $2^{20}$ subsets of the ordinary pool in each of two cases, first without the seven and then with the seven contracted. Whenever it has found coverage for a proper subset, it propagates that fact upward and skips the current set. At the second stage it also initializes the table with the minimal ordinary covers. A positive set missed by the proper-subset test is minimal under deletion of an ordinary modulus. Deletion of a 7-multiple leaves one section without any such class, and the ordinary moduli alone cannot cover. The remaining decision tests use the exact five-section procedure described in the previous enumeration. Necessary fibre and reciprocal tests are applied to candidates only after covering proper subsets have been excluded, so a rejected failure of the fibre condition cannot hide a new minimal cover. In the contracted case this applies to the list including the distinct extra modulus 120.

There are 3,835 minimal ordinary sets and 6,314 minimal expansions, hence 10,149 sets in total. Restricting the full list to cap 56 reproduces the earlier 4,356 sets exactly. As a further cross-check the original contraction search and the five-section search independently returned identical lists of all 1,444 sets through cap 55.

## Bounds beyond 25

Every 26-subset of the candidate pool at cap 69 contains an already enumerated cover of smaller cardinality. Thus $m(26)\ge70$. The same subset test gives $m(27)\ge72$, $m(28)\ge80$, $m(29)\ge84$, $m(30)\ge90$ and $m(31)\ge96$. These are lower bounds. The witness at size 25 also gives $m(26)\le96$. Replace 48 by 32 and 96. They are the only two moduli in the resulting list divisible by 32 and contract to a single modulus $\operatorname{lcm}(16,48)=48$. Deleting either one forces the other classes alone to cover, which would give a cover after deleting 48 from the original set. Any other deletion contracts to the corresponding deletion in the original set. The new list is therefore irreducible.

## Reproduction

In the directory containing the companion programs, use Python 3.10 or later:

```sh
python section_solver.py 55
python at56.py
python saturated60.py
python check60.py
```

The final check exhausts the periods of the two displayed residue assignments, runs every one-modulus deletion through the decision procedure, compares the cap-56 tables, and verifies the six stated exclusions. To compare the two cap-55 methods, run `python enumerate_covers.py 55` and compare the sets of tuples in `covers-through-55.json` and `section-55.json`. An exact formula for arbitrary cardinality remains open in this work.
