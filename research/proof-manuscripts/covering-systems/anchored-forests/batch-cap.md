# Joint hole counts for complete batches of congruence classes

Codex (OpenAI), November 28, 2026. AI-authored written partial result for Erdős #1189(ii).

Let D be an irreducible covering set of k distinct moduli, with greatest modulus X. Its lcm need not belong to D. Reserve any one row. Assign every other modulus n to its largest prime q and exponent $j=v_q(n)$. Partition each such group into disjoint batches of exactly q rows and fewer than q leftover rows. For a batch B write $g_B=\operatorname{lcm}_{n\in B}(n/q)$. Its rows see the lower $j-1$ digits at q through their cofactors; their common free digit is the j-th one.

**Joint bound.** Take any nonempty collection of complete batches. Fix any single assignment to all nonreserved rows outside the collection. Among the remaining holes of that assignment let $b_B$ be the number of residues modulo $g_B$, and T the number of residues modulo the lcm of all the $g_B$ in the collection. Then
```math
    b_B\ge2\quad(B\text{ in the collection}),\qquad
    1\le T\prod_B(1-1/b_B),\qquad \sum_B 1/b_B\le\log T.              \tag{1}
```
All these numbers are finite and positive by periodicity and irreducibility. Assignments can be optimized separately for different collections.

For each batch choose a target among its $b_B$ residues. B can cover every lift of that target: match the target modulo n/q in each row n and assign the j-th q digit a different label in each of the q rows. These prescriptions give legal residues modulo each n, including when j>1. Any point over the chosen target matches the row for its j-th digit. Disjoint batches can execute these placements simultaneously even if one batch tests another's free digit. For uniformly and independently chosen targets, any one of the T joint patterns escapes the targets with probability $\prod_B(1-1/b_B)$. There must always be at least one escaping pattern or the reserved row could be omitted. Expectation gives the product bound and excludes $b_B=1$. Taking logarithms gives the sum bound. A finite abstract example attains the product equality: on $\{0,1\}^r$ let each of r batches target one bit. Every vector of choices leaves exactly the complementary bit string. This example shows sharpness of the product counting step.

**A bound at cap X.** Use dyadic bins $Q\le q<2Q$, separating first positions $i=1$ from higher positions $i=2$. For each nonempty bin and type use its complete batches as one collection. Write $B_{Q,i}$ for an upper bound on their largest $b_B$ in some single complementary assignment for that collection, and $T_{Q,i}$ for its joint count in that same assignment. Then
```math
 k\le 1+F(\sqrt X)+O(X^{2/3}\log X)
       +2\sum_{Q,i} Q B_{Q,i}\log T_{Q,i},\qquad
 F(t)=\sum_{p\le t}(p-1).                                                  \tag{2}
```
Indeed (1) bounds the number of complete batches in a bin by $B_{Q,i}\log T_{Q,i}$. There are fewer than 2Q rows in each. If $q^e$ is the highest power of q in the period, at least q distinct original moduli must be divisible by $q^e$: the other rows leave a hole in a successful placement, and varying that highest digit leaves a full fibre. Distinctness gives $q^{e+1}\le X$. Thus the first-position leftovers total at most $F(\sqrt X)$, and all higher leftovers total at most $\sum_{q\le X^{1/3}} q\log_2 X=O(X^{2/3}\log X)$. The reserved row accounts for the one.

In particular the following class has sharp leading bound $k\le(1+o(1))X/\log X$. Assume fixed $0<\eta\le\theta<1$, $A\ge0$ and C. Only the complete batches need satisfy these conditions:
* In a first-position bin all batch cofactors have prime factors at most $C Q^{1-\theta}$, and $b_B\le C Q^{\theta-\eta}(\log(2X))^A$ under one assignment for that bin.
* In a higher-position bin $b_B\le C Q^{1-\eta}(\log(2X))^A$ under one assignment for that bin.

A collection of cofactors at most X with all primes at most y has joint log-pattern count at most $\pi(y)\log X$. Apply this with $y=C Q^{1-\theta}$ in the first bins and $y=2Q$ in the second. The two dyadic sums in (2) are respectively $O(X^{1-\eta/2}(\log(2X))^{A+1})$ and $O(X^{1-\eta/3}(\log(2X))^{A+1})$, since their ranges end at $\sqrt X$ and $X^{1/3}$. Both are $o(X/\log X)$. The prime number theorem gives $F(\sqrt X)\sim X/\log X$. In particular the greatest modulus is at least $(1-o(1))k\log k$ in this class. The condition allows a polynomial number of visible residues in individual first-position batches when η<θ.

**Sharpness along an explicit sequence.** Let z tend to infinity through primes and $L=\operatorname{lcm}(1,\ldots,z-1)$. Take the old digits $(p,j)$ ordered by increasing p and then j, for $p^j\mid L$, $j\ge1$. At that position take the $p-1$ moduli $p^j d$, $1\le d<p$. Their other tests only involve earlier positions. Align those tests at zero and give the new digit the $p-1$ nonzero labels. Induction leaves just zero modulo L. Add z terminal rows $zd$ for $1\le d<z$ and for the smallest multiple of 6 greater than z (assume $z\ge11$). This additional d is at most z+6 and divides L: each maximal prime power dividing it is at most $d/2\le z-1$ since d has at least two prime factors. The terminal guards have lcm L. Align them at zero and use all z labels at the new prime. Distinctness follows from the largest prime and its exponent, and then the distinct cofactor.

In any reassignment, every old surviving prefix has a child since at most $p-1$ rows test its new digit at its stage. An old deletion leaves at least two complete old holes since at that stage every prefix has at least two children. To finish with z terminal rows their labels must all differ, and then each old hole must agree with every terminal guard. Their lcm L permits at most one old hole. Deleting a terminal also fails since a label is missing and at least one old hole survives. This proves irreducibility with all residues free to change. Reserving one terminal leaves exactly $p-1$ rows in every old group and $z-1$ in the new one, hence no complete batches. The largest modulus is between $z^2$ and $z(z+6)$; size is $1+\sum_{p^j\mid L}(p-1)+(z-1)\sim F(z)$, where the sum is over $j\ge1$ and higher powers contribute $O(z\log z)$. These sets attain the leading constant. Digit-stage constructions and their antecedents, including Sun's covering-number constructions, are discussed in the [earlier manuscript](../reciprocal-sums/grouped-digits.md).

For arbitrary irreducible sets we do not yet have the common complementary assignments controlling the quantities in (2). A direct next target is to bound the joint cost $B_{Q,1}\log T_{Q,1}$ for nearly balanced prime pairs. The [joint guard distribution](joint-guard-distribution.md) treats a related cut for the reciprocal problem.

[Lean proof of simultaneous targeting and the finite product inequality](JointBatch.lean). [Independent arithmetic checks and construction verification](joint-guard-check.py).

[Star Fleet Math](https://www.starfleetmath.com/) reports checked unrestricted near-linear bounds giving $m(k)=k^{1+o(1)}$. The logarithmic factor in the unrestricted lower bound is a finer question. The existing [every-size construction](../reciprocal-sums/) supplies a written $m(k)\le(1+o(1))k\log k$ upper bound.
