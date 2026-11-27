# The minimum largest modulus for 31, 32 and 33 classes

Codex, at the request of Jordan Pollard · 27 November 2026 · research submission for review

Write $m(k)$ for the least possible largest modulus among irreducible covering sets of $k$ distinct integers greater than one. After deleting a modulus, all the other residues may be freely reassigned. The new values are

| Number of moduli | 31 | 32 | 33 |
|---|---:|---:|---:|
| Minimum largest modulus | 96 | 108 | 108 |

There are exactly two minimizing sets at size 31. In the 35-element pool below they omit, respectively, $\{2,3,8,9\}$ and $\{2,3,8,18\}$. Thus one exchanges 9 for 18. [First residue assignment](witness31-96.jsonl) · [Second residue assignment](witness31-96-second.jsonl)

## Pools and earlier facts used in the exclusion

Let $P_c$ be the potential moduli at cap $c$. If $p^a$ is the full power of $p$ in the period of an irreducible set, at least $p$ different moduli must contain it. Their cofactors are coprime to $p$, giving $(p+1)p^a\le c$. Thus $P_c$ consists of the admissible divisors up to $c$ of the product of the largest such prime powers. The [preceding finite search](cap96-fibres.md) gives

$$
P_{96}=\{2,3,4,5,6,7,8,9,10,12,14,15,16,18,20,21,24,28,30,32,35,36,40,42,45,48,56,60,63,70,72,80,84,90,96\}.
$$

We have $P_{95}=P_{90}=P_{96}\setminus\{32,96\}$, $P_{104}=P_{96}$, $P_{107}=P_{105}=P_{96}\cup\{105\}$ and $P_{108}=P_{105}\cup\{27,54,108\}$. Every 31-subset at cap 95 contains a smaller covering set. The only **noncovering** 30-subsets of $P_{90}$ are $X=P_{90}\setminus\{2,3,4\}$ and $Y=P_{90}\setminus\{2,3,6\}$. The latter fact follows from the previous exhaustion: a 30-subset passing the smaller-cover exclusions must use all six entries above cap 60 and a noncovering choice of 24 old entries. At size 29 the earlier results leave only these two choices whose cap-84 subfamily fails to cover; both whole cap-90 sets fail as well. The other 24-entry choices already have covering subfamilies. [Cap-90 calculation](quick30.py) · [Decisions](quick30-results.txt) · [Cap-95 exclusion](../reciprocal-sums/finite-60.md)

The two rows 32 and 96 can be replaced by one virtual row 48. Indeed they are the only rows fixing the highest binary digit, and their projections have moduli 16 and 48. If the other rows have a hole, each of its two lifts must be covered. One top row is needed on each side and the hole lies in their intersection, a class modulo 48 if nonempty. Conversely an assignment with that class lifts. One top row alone cannot help coverage of the lower rows. These statements hold for coverage decisions and all single deletions.

## Exact exclusion at 31

The lower bound at 95 leaves cap 96 as the first possibility. A minimizing candidate must contain 32 and 96 by the preceding contraction. It must contain the original 48 as well. Otherwise contracting would give a 30-element set of distinct moduli at cap 90. A cover after deleting any of its ordinary entries would lift. A cover after deleting its virtual row would cover with the original lower entries alone. Thus the contracted set would be irreducible, contradicting $m(30)=96$.

From the four-element omissions in $P_{96}$ that preserve those three entries, discard all sets that contain any covering subset in the previous cap-60 catalog, the recorded size-26 to size-30 examples, or the cap-84 census used by the verification script. This leaves 258 candidates. In 205 a specified single deletion is still coverable. A further 51 whole sets cannot cover. The other two cover, and all 31 single deletions of each fail even after reassignment. The table gives the omitted moduli and the outcome of every remaining candidate. The two witnesses each cover all 10,080 residues of their period. [Census](census31-32.json) · [Reproduction script](verify31_33.py) · [Lean proofs of coverage for every integer](Size31Minima.lean)

## Why sizes 32 and 33 both jump to 108

At cap 96 a noncovering 32-set must contain both 32 and 96. Without both it contains at least 31 old entries from $P_{90}$, and these have a covering subset. With both it must extend either $X$ or $Y$. Put $A=X\cup\{32,96\}$ and $B=Y\cup\{32,96\}$. An exact decision finds that $A$ fails to cover, while $B\setminus\{90\}$ already covers. Every other 32-set at cap 96 contains a smaller cover by the same old-pool test. Thus no 32-set is irreducible at cap 96, and $A$ is its unique noncovering 32-set. [Explicit proper cover in the second case](witness32-proper.jsonl)

At size 32 and cap 105 an irreducible set must introduce 105. It must contain both 32 and 96: a lone top binary row is redundant, and with neither the set contains 31 members of $P_{90}$. Removing 105 leaves a noncovering 31-set. If that set contains 48, it is one of the 51 noncovers from the size-31 census, since all sets discarded before the census contained a cover. If it lacks 48, contraction produces one of the two noncovering distinct 30-sets $X,Y$ at cap 90. Inverting this contraction gives exactly two more candidates. On adding 105, **46 of the 53 whole sets fail to cover and seven have a coverable single deletion**. This excludes size 32 up to 107.

At size 33 and cap 105 any irreducible set must include 105: every 33-subset at cap 96 contains a covering 32-subset since only $A$ is noncovering. Removing 105 must leave $A$. The sole candidate $A\cup\{105\}$ fails to cover, excluding size 33 up to 107. In particular one cannot deduce these exclusions from monotonicity in $k$; each cardinality was checked.

For the upper bounds, start from the [size-30 example](witness30.jsonl) or the first size-31 example above. Each contains 36. Replace it by 27, 54 and 108. These are exactly the three rows seeing the highest ternary digit and their projections 9, 18 and 36 have least common multiple 36. Their contraction therefore recovers the original cover. Removing any ordinary entry contracts to an impossible old deletion. Removing a new entry leaves an unserved ternary section, which would require the old rows apart from 36 to cover on their own. This proves irreducibility of the resulting size-32 and size-33 examples, which both have maximum 108 and period 30,240. [32 residues](witness32-upper108.jsonl) · [33 residues](witness33-upper108.jsonl) · [Lean proofs of all-integer coverage](Size32And33At108.lean)

## What the exclusions give at the next sizes

At sizes 34 and 35, attaining cap 108 would require all of 27, 36, 54 and 108. The three new entries are indispensable or else the previously eligible rows would have to cover on their own. If the original 36 were absent, contraction would yield an irreducible set of distinct moduli of size 32 or 33 at cap 105, which the exclusions above forbid. Thus the next computation must handle a repeated virtual row 36.

At size 36 and cap 108 there is only one candidate, $A\cup\{105,27,54,108\}$. Its 33 old entries must be noncovering, and $A\cup\{105\}$ is the only noncovering 33-set at cap 105. Every 34-subset at cap 105 therefore already contains a cover. A set of at least 37 entries from $P_{108}$ has at least 34 such old entries. The pool first changes again at 112, so $m(k)\ge112$ for $k\ge37$. No decision for the single size-36 candidate is claimed here.

## How the new decision is checked

After the top binary contraction the two copies of 48 are treated as distinct. For the next binary digit the at most four projected rows form a sublist of $(8,24,24,40)$. A possible hole must be covered on both binary sides. With all four rows there are two sufficient families of masks on the 120-cycle. One allows an arbitrary class modulo 24 together with an arbitrary class modulo 40. Put a 24-row on each binary side over the first class, and put 8 and 40 on opposite sides over the second. The other, inside one class modulo 8, allows two of its three 24-classes together with one of its five 40-classes. It has 120 translates. The [preceding fibre lemma](cap96-fibres.md) proves exhaustiveness. The accompanying checker enumerates both sides and all residues for every sublist, compares the resulting sets against the masks used by the program, and tests containment in both required directions. [Binary mask audit](audit-binary96.py)

The primary solver eliminates the seven sections and the highest ternary digit, then tests the remaining ordinary rows and the compound binary masks on the 120-cycle. All seven possible cofactors through 60, as well as the higher ones up to 15 at cap 105, divide 360. There are at most eleven 7-rows. In every assignment with a common ordinary hole, each of the seven sections needs a row and at least one section is a singleton. This justifies the existing seven-bucket enumeration also at cap 105.

A further exact symmetry identifies equivalent masks. Regard the 120-cycle as $\mathbb Z/8\times\mathbb Z/3\times\mathbb Z/5$. Swap the two children at any of the seven internal nodes of the binary digit tree, and independently permute the 3 and 5 coordinates. All ordinary congruence choices and every translated compound-row family are preserved. Sorting the five columns accounts for all $5!$ permutations. Testing the 128 binary-tree automorphisms and six ternary permutations gives the remaining action. Either representative of an orbit gives the same decision. A second solver checks both size-31 examples using a seven-section/binary projection and a remaining 180-cycle. The two solvers share the native final residue search. The Lean files certify size, distinctness, largest modulus and coverage; the deletion and exclusion proofs are computational.

## Reproduction

Run in this directory with Python 3.10 or later and a C++20 compiler. The cap-60 catalog is generated by `saturated60.py` in the sibling `reciprocal-sums` directory. Pass its path as the argument below.

```sh
g++ -std=c++20 -O3 -shared -fPIC holecheck.cpp -o holecheck.so
g++ -std=c++20 -O3 -shared -fPIC maskcombine.cpp -o maskcombine.so
g++ -std=c++20 -O3 -shared -fPIC symmetry120.cpp -o symmetry120.so
python audit-binary96.py
python verify31_33.py ../reciprocal-sums/full-60.json
python check31_binary.py minimizers31.json
lean Size31Minima.lean
lean Size32And33At108.lean
```

The census counts minimizers only at size 31. The general extremal function and the sharp unrestricted reciprocal coefficient remain open in this work.
