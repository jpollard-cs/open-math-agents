# Five exact minimum largest moduli from a prime-11 extension

Codex, at the request of Jordan Pollard · 27 November 2026 · written and computational proof for review

An irreducible covering set is a finite set of distinct moduli greater than one that covers the integers under a suitable choice of residues and loses this property on deleting any modulus, even if all remaining residues are chosen afresh. Write $m(k)$ for the least possible largest modulus at size $k$.

**Theorem.** $m(39)=m(40)=m(41)=m(42)=m(43)=132$. Every irreducible set of size at least 39 has largest modulus at least 132. Ten constructions at cap 132 also improve the bounds below.

| Size | 34 | 35 | 36 | 37 | 38 | 39–43 |
|---|---:|---:|---:|---:|---:|---:|
| Lower bound | 108 | 108 | 112 | 120 | 126 | 132 |
| Upper bound | 132 | 132 | 132 | 132 | 132 | 132 |

The lower and upper bounds come from different arguments. No monotonicity of $m$ is assumed. The [problem statement](https://www.erdosproblems.com/1189) asks for the unrestricted minimum and maximum at every cardinality.

## Why cap 131 cannot accommodate 39 moduli

The earlier [size-36 exclusion](size36-cap.md) and [cap-105 census](minima-31-33.md) give a stronger property than the absence of a size-36 irreducible set. **Every** 36-subset of the eligible pool $P_{108}$ contains a proper covering subset. Indeed, the three new entries over $P_{105}$ are 27, 54 and 108. A 36-subset has at least 33 old entries. There is just one noncovering 33-subset $H$ of $P_{105}$. Any 34 or more old entries contain several distinct 33-subsets, so one covers. If the 33 old entries are exactly $H$, the only candidate is $H\cup\{27,54,108\}$. It contains the explicit [33-modulus proper cover](size36-proper-subset.json).

If $p^a$ is the full power of $p$ in the period of an irreducible covering set, at least $p$ distinct moduli must be multiples of $p^a$. Their cofactors are coprime to $p$. Hence $(p+1)p^a$ cannot exceed the cap. Enumerating the divisors allowed by this condition gives
$$
P_{131}=P_{108}\cup\{112,120,126\}.
$$
Up to 131 the only eligible primes are 2, 3, 5 and 7, with exponents at most 5, 3, 1 and 1 respectively, constant over the entire interval from 108. The new entries first occur at their own values. A set of size at least 39 under cap 131 thus has at least 36 entries from $P_{108}$, which already contain a cover. At caps 111, 119 and 125 the corresponding thresholds are 36, 37 and 38. After the eleven prime-11 entries appear at 132, the pool stays fixed through 134. The same count therefore gives $m(k)\ge135$ for every $k\ge50$. This leaves sizes 44–49 as the only possible extensions of the run of exact values to the right. The lower bounds at sizes 34 and 35 follow from the earlier cap-107 exclusion, since any 34 old entries contain a covering 33-subset.

## Replacing one indispensable modulus with eleven

Let $A$ be an irreducible covering set, $d\in A$ and $D$ a multiple of $d$. Suppose that for some assignment the points missed by $A\setminus\{d\}$ are all in a single class modulo $D$. Replacing $d$ by $D$ preserves coverage; any new covering assignment of a proper subset would project to one of a proper subset of $A$ because $d\mid D$. In our applications $D$ is distinct from all ordinary moduli.

More generally let $p$ be prime, coprime to the period of the ordinary moduli and to $D$. Choose $p$ distinct divisors $c_0,\ldots,c_{p-1}$ of $D$ whose least common multiple is $D$. Replace the distinguished class by $p$ classes with moduli $pc_i$. Translate its residue modulo $D$ to zero first. The assignments $p c_i$ with residues $D i\bmod p c_i$ cover all multiples of $D$, since $D(t-i)$ is divisible by $pc_i$ when $t\equiv i\pmod p$.

For the converse, the ordinary moduli alone cannot cover under any reassignment. At an ordinary hole, varying the independent coordinate modulo $p$ gives $p$ holes. All $p$ new classes are necessary, and each must serve a different coordinate. Every ordinary hole must therefore satisfy the projection of **each** new class modulo its $c_i$. These projections have a common solution and their intersection is one residue class modulo $D$. Contracting them to that class gives a covering assignment on the old ordinary subset together with $D$. The preceding projection to $d$ forces every old ordinary modulus to be present. This proves irreducibility with freely reassigned residues.

Here $p=11$, $D=2520$ and the cofactors are $1,2,3,4,5,6,7,8,9,10,12$. These are also exactly the eleven new moduli divided by 11 when the cap increases from 131 to 132. The extension adds ten moduli. All ordinary entries in the examples below are at most 108.

## The ten seeds and their certificates

For each size 24 through 33 the [seed data](prime11-seeds.json) give one complete residue assignment and the distinguished modulus $d$. All assignments have been translated so the holes after deleting $d$ are zero modulo 2520. The row $d$ divides 2520 in every case. Checking every residue in one period establishes the hole condition. For example, for the 33-element seed the 12 ordinary holes in a period of 30,240 are precisely the multiples of 2,520 there. Replacing its modulus 35 by the eleven new rows gives a 43-element irreducible cover.

| Seed size | 24 | 25 | 26 | 27 | 28 | 29 | 30 | 31 | 32 | 33 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Distinguished modulus | 7 | 7 | 40 | 40 | 28 | 28 | 28 | 28 | 28 | 35 |

The size-24 and size-25 moduli are from the [cap-60 catalog](../reciprocal-sums/finite-60.md). We reran every one-modulus deletion at both sizes with the earlier exact reassignment solver. For sizes 26 through 33 the verifier compares the full modulus sets with the earlier irreducible examples, including the [alternative size-28 and size-31 examples](cap96-fibres.md) and the [size-32 and size-33 examples](minima-31-33.md). We also reran every deletion for the six distinct larger base sets after contracting the saturated top ternary digit where present. Some displayed residue choices differ from the original certificates. Irreducibility is a property of the modulus set.

The [Python verifier](check-prime11.py) checks the holes, the covering assignments over all periods, the cap-pool increments, and the final combinatorial deduction from the published census. Use `python check-prime11.py --seeds` to repeat the cap-60 deletion tests at every seed size 18–25 as well. With the earlier cap-96 C++ verifier compiled as in [the census](minima-31-33.md), use `--all-seeds` to replay every larger seed check too. Add `--export DIRECTORY` to write out every modulus-residue pair for each new size. [Verification output](prime11-checks.txt)

There is a second sharp consequence when the period must be divisible by 11. Under cap 132 such a cover must contain all eleven multiples listed above, so its period is divisible by $11\cdot2520=2^3 3^2 5\cdot7\cdot11$. The Znám–Simpson period bound gives $k\ge1+3+4+4+6+10=28$. Below cap 132 the prime 11 is impossible by the fibre bound. Additional sharpened seeds at sizes 18 through 23, included in the same JSON file and checked by the same program, give every size 28 through 33 after the extension. Thus the least possible cap with prime 11 present is **exactly 132 at every size from 28 through 43**, and 28 is the first possible size at that cap. The general prescribed-prime optimization appears in the [prime-budget manuscript](../prime-budget/README.md). The contiguous size range here uses explicit constructions.

The independent [Lean file](Prime11Coverage.lean) proves all-integer coverage, distinctness, size and largest modulus for the ten examples of sizes 34–43. Run `lean -j1 Prime11Coverage.lean` with Lean 4.33.1 to reproduce the [kernel check](prime11-lean-check.txt). The irreducibility transfer has the written proof above. The lower-bound census and its earlier deletion searches retain their original computational status. The exact values for sizes 34–38 and the general formula for $m(k)$ remain open in this work.
