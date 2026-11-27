# Excluding largest modulus 108 at size 36

Codex, at the request of Jordan Pollard · 27 November 2026 · research note for review

Let $m(k)$ be the minimum largest modulus of an irreducible covering set with $k$ distinct moduli greater than one, allowing reassignment of all residues in a subset.

**Every irreducible covering set with at least 36 moduli has largest modulus at least 112.** This adds the case $k=36$ to the previous exhaustion for $k\ge37$. We also give constructions with largest modulus 150 for each $k=34,35,36,37$. In particular $112\le m(36)\le150$.

## A proper subset of the last candidate covers

The [previous finite census](./minima-31-33.md) proved that the only noncovering 33-set from the eligible pool through 105 is $H=(P_{96}\setminus\{2,3,4\})\cup\{105\}$. At caps 106 and 107 the pool stays fixed. At cap 108 the three additional eligible entries are 27, 54 and 108. Any 34-subset of the old pool contains a covering 33-subset, since at most one of its 33-subsets can equal $H$. Thus every size-36 candidate must be $G=H\cup\{27,54,108\}$. Every larger set in the pool contains a covering proper subset as well. The next change of eligible pool occurs at cap 112.

In fact $G\setminus\{56,63,80\}$ already covers all integers. The 33 [explicit modulus-residue pairs](./size36-proper-subset.json) have period 30,240. The [Lean certificate](./Size36ProperDeletion.lean) checks all residue classes, then lifts to arbitrary integers by periodicity. The [Python checker](./check-size36.py) independently marks every covered residue and compares the modulus set to the prior census. This settles the last candidate by a positive certificate. No monotonicity in $k$ is required.

## Four constructions under cap 150

Take the previously established [size-30](./witness30.jsonl), [size-31](./witness31-96.jsonl), [size-32](./witness32-upper108.jsonl) and [size-33](./witness33-upper108.jsonl) examples. Each contains 60 and has precisely one factor of 5 in its period. Replace 60 by the five moduli $25,50,75,100,150$. Dividing these five by 5 gives $5,10,15,20,30$, with least common multiple 60. Give each new row one of the five values of the second base-5 digit. For its remaining coordinates use the projection of the old residue modulo 60. All points formerly covered by 60 are then covered by the new rows.

To prove irreducibility under reassignment, consider any putative proper covering subsystem. If the ordinary rows cover by themselves, the old irreducible set covers after deleting 60, which is impossible. Otherwise there is a point missed by the ordinary rows; varying its second base-5 digit preserves that property. All five new rows must therefore be present and use distinct values of this digit. Every ordinary hole must lie in the intersection of their five projected congruences. That intersection is nonempty and gives a single class modulo 60 by the generalized Chinese remainder theorem. Replacing the five rows by this class yields an old cover. Irreducibility forces every old row to be present, proving the claim. The construction increases size by four and gives maximum 150 at each indicated size.

To verify coverage of the deletion certificate and the four constructions, run `python check-size36.py` in this directory. The first assertion about the set of candidates uses the linked exhaustive census. This note supplies bounds at sizes 34–37; the exact minima at these four sizes remain undetermined here.
