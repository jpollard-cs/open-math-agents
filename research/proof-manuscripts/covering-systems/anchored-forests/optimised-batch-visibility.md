# Large projections in every partition at the leading minimum-modulus scale

Codex (OpenAI), November 28, 2026. Written research on Erdős #1189(ii) and (iii) for contributor-fork public review.

Let an irreducible covering set consist of distinct integers greater than one. Some assignment of one residue per modulus covers the integers, and no proper subset admits any such assignment. Write X for its greatest modulus, k for its size, and S for the sum of its reciprocals. Let R₀(k) denote the largest such sum among the zero-defect sets of size k. Use the [batch sieve](batch-cap-sieve.md): reserve any one row, put aside squares of the largest prime and rows with two different primes above the chosen cutoff Y, then partition the remaining rows with largest prime q into batches of q with fewer than q left over. In one dyadic prime bin, remove all its complete batches and the reserved row. Assign arbitrary residues to all remaining rows. For a batch B at q let b(B) be the number of residues occupied by the surviving holes modulo the lcm of the integers n/q for n in B.

**Theorem.** For every fixed t>0 there are genuine irreducible sets and primes p tending to infinity with

$$
 X\sim k\log k,\qquad S=R_0(k)+o(1),\qquad
 \log(\sqrt X/p)\sim t\sqrt{\log X}.
$$

In the bin containing p, for **every** choice of reserved row, **every** allowed partition and **every** common assignment to the remaining rows, one of two complete p-batches has
$$
              \log b(B)\ \ge\ (1/4-o(1))\sqrt p.
$$
For this family the minimum of the maximum of the two log counts over all three choices is asymptotic to $\sqrt p/4$. This is an exact asymptotic for this family. The global extremum over all systems is undetermined. The construction works for every sieve cutoff $X^{3/8}\le Y\le\sqrt X$, including the critical cutoff with parameter t.

There is also a specified squarefree product G of primes such that deleting **all** multiples of p leaves holes projecting onto **every** class modulo G, under every assignment to the surviving rows, with $\log G\sim\sqrt p/2$. For assignments obtained from a successful cover the [critical deletion bound](critical-deletion.md) simultaneously gives hole density at most $\exp(-\exp((1-o(1))J))$, where $T=\lceil X/p\rceil$, $v=\log(T/p)$ and $J=(\log T)\log(v)/v$. Thus optimizing the choice of partition and the common assignment cannot give uniformly small projections, even among zero-defect systems on the leading cap scale with asymptotically optimal zero-defect reciprocal mass. Our examples have only two complete batches at p. The question of how many rows can belong to such batches in a cover beating the cap remains open.

## Stages of the construction

Take a large prime p. Choose a prime $z\sim p\exp(t\sqrt{2\log p})$ by the prime number theorem. Set $A=\lfloor\sqrt p\log p\rfloor$ and $M=\operatorname{lcm}(1,\ldots,A)$. Starting immediately above A, take consecutive primes r until $U=\sum_r(r-1)\ge p+2$ for the first time. Denote this set by E, its largest element by C, and its product by G. For every fixed positive δ the primes between A and $(1+\delta)A$ have total cost of order $A^2/\log A\gg p$ by the prime number theorem. Therefore
$$
 C\sim A,\quad p+2\le U<p+2+C,\quad |E|\sim p/A,\quad
 \log G\sim (p/A)\log A\sim\sqrt p/2.                       \tag{1}
$$

1. Install every prime digit $s^j\mid M$, ordered by increasing prime and then exponent. At this digit use the $s-1$ moduli $s^j d$, $1\le d<s$.
2. Install the first p digit with $p-1$ moduli $pd$, choosing distinct divisors of M through $4p$. For each r in E install its first digit with $r-1$ moduli $prd$, choosing distinct divisors of M through $2C$. All of these moduli have largest prime p and exactly one factor p. Their cofactors see at most one member of E, namely r in its own group.
3. Complete all as-yet uninstalled positions $s^j\le z$ in increasing prime and then exponent order, except the last prime z. Again use $s^jd$ for $1\le d<s$. At the last prime z use $zd$ for $1\le d<z$ together with z times the least multiple of six strictly greater than z.

Here and throughout, a prime digit $s^j$ means the j-th base-s digit in the Chinese remainder representation of a residue. The distinct guards in step 2 exist. Through $4p$, integers failing to divide M contain either a prime above A or a proper prime power above A. A union bound for the former costs at most $4p(\log 2+o(1))$, by the prime reciprocal sum between A and $4p$. For the latter, the sum of reciprocals of all proper prime powers above A is $o(1)$, by convergence of their full reciprocal series. Since $4(1-\log 2)>1$, more than p divisors are available. Through $2C=O(A)$ the prime reciprocal sum from A to $2C$ tends to zero, so $(2-o(1))C$ integers there divide M. In step 1 the guards $d<s$ divide the preceding period since all their required powers are at most A. In step 3 all powers of smaller primes needed by $d<s$ are already installed. The final extra guard divides $\operatorname{lcm}(1,\ldots,z-1)$: it has at least two prime factors of different bases, and its largest constituent prime power is at most $(z+6)/2\le z-1$.

No modulus repeats. Each stage uses distinct moduli testing its new digit, which all previous stages omit. The maximum is the terminal modulus $X=z(z+O(1))$: the special rows are at most $\max(4p^2,2pC^2)=o(z^2)$, and ordinary nonterminal rows are below $z^2$.

**Arbitrary reassignments.** In the aligned placement all earlier guard digits are zero, and the side rows use the distinct nonzero labels of the new digit. This leaves exactly zero after each nonterminal stage. The final z rows cover all z labels there. Conversely each surviving prefix in any placement has a surviving child at every nonterminal stage. With one missing row from such a stage a prefix has at least two children, hence at least two different prefixes survive to the terminal. To cover all labels at either prefix the terminal rows must have distinct z labels and every guard must hit that prefix. Their guards have lcm equal to the entire previous period, so they cannot all hit two distinct prefixes. A terminal deletion leaves a label uncovered over any surviving prefix. This verifies irreducibility for the original unrestricted reassignment quantifier. This use of prime stages follows the [previous constructions and credits](../reciprocal-sums/grouped-digits.md), including Sun's sufficient covering-number construction.

## Projections with every choice allowed

Exactly $p-1+U$ rows have largest prime p. They all survive the arithmetic thinning: their possible second prime is at most $C=X^{1/4+o(1)}$, and none tests the second p digit. Other prime owners in the dyadic bin of p have at most $q-1$ first-position rows each. Indeed z lies in a different bin eventually, and the only transfers of first-position rows were from E into the p group. Consequently exactly two complete batches form in this bin, even after reserving any one row. Outside these two batches there are $U-p-1=O(C)$ original p-owned rows, counting a reserved p-row as outside. This number is less than $p-1$.

Fix any residues on the complement. Every choice of the first labels at **all** r in E extends to an integer missed by the complement. Pick a surviving old prefix modulo M; step 1 always leaves one. Choose the p label different from all the outside p-owned rows' labels and different from the p residue tested by the terminal row $zp$ if that row is present. This is possible since fewer than $p-1$ labels were forbidden before the terminal test. Now prescribe the r labels arbitrarily. All surviving rows of step 2 miss by the p coordinate. Through step 3, every ordinary stage has a free child for each surviving prefix, including a higher digit above one of the prescribed r labels. At the terminal there are at most $z-1$ active rows since $zp$ is absent or misses. Some final label survives. The Chinese remainder theorem gives the integer. The same argument with every multiple of p deleted proves the full projection statement for that deletion, even with no row reserved.

The first labels at r that a batch tests therefore vary independently on its projection. If r is absent from both batches, all its $r-1$ special rows lie outside, so only $O(C/A)=O(1)$ primes of E can be absent. The product of the two counts is at least $G/\exp(O(\log p))$, proving the stated lower bound with (1). This bound is uniform over the residue assignments and the other choices.

To attain the matching upper bound, reserve a terminal z-row, put alternate primes r of E in two groups, and assign every special row for a given r to its group's batch. The cost sums differ by $O(C)$ and the sums of logs by $O(\log C)$ by monotonicity. Each cost is therefore $p/2+O(C)<p$. Fill both batches to p with different ordinary p-stage rows; the required number is $2p-U\le p-1$. Align the old rows of M in their usual placement. All holes lie over zero modulo M. The cofactor lcm of either batch divides M times the product of its own primes r, proving the upper bound. In this choice all other bins have no complete batches after reserving a terminal row.

## Size and reciprocal mass

Write $H_n=\sum_{i=1}^n1/i$. There are exactly $k=1+\sum_{s^j\le z}(s-1)$ rows, summing over prime powers with $j\ge1$. This is the zero-defect cardinality of the period. The prime number theorem gives $k\sim z^2/(2\log z)\sim X/\log X$. Higher powers contribute $O(z\log z)$ by summing over bases at most $\sqrt z$. The [zero-defect prime-position estimate](transfer.md) at these sizes gives
$$
 R_0(k)=\sum_{s^j\le z}H_{s-1}/s^j+o(1).
$$
One can also compare the ordinary aligned construction at the identical cutoff z and use its additive-$o(1)$ optimality. Every nonspecial stage delivers its entire summand (and the terminal one extra row). The p-stage costs at most $H_{p-1}/p=o(1)$ in lost mass. The loss at the transferred primes is at most
$$
 \sum_{r\in E} H_{r-1}/r\sim (p/A)(\log A)/A\sim 1/(2\log p).
$$
Upper optimality follows from zero defect. This proves the simultaneous reciprocal assertion. In particular the rare-hole bound from the earlier critical deletion theorem and the lower bound for every partition concern the very same systems and cap regime.

**A fixed additive tradeoff.** Alternatively set $A=\lfloor a\sqrt{p\log p}\rfloor$ for a fixed $a>0$. The prime number theorem and the stopping rule give $C\sim\sqrt{a^2+1}\sqrt{p\log p}$ and $\log G\sim(\sqrt{a^2+1}-a)\sqrt{p\log p}$. All the guard counts and proofs above apply since $C/A$ is bounded. The optimal log visibility of the two batches is $(1/2+o(1))\log G$. The reciprocal deficit $R_0(k)-S$ now tends to $\log(\sqrt{a^2+1}/a)$. In fact the removed ideal mass is $\sum_{A<r\le C}H_{r-1}/r=\log(C/A)+o(1)$ by partial summation over the fixed ratio interval. The new special mass is at most $|E|/p=o(1)$. Thus a fixed positive allowance buys a constant multiple of $\sqrt{p\log p}$ in log visibility.

[Independent finite checks and the 57-modulus example](batch-visibility-check.py). The asymptotics and their arbitrary-assignment proof are written. The local-lemma deletion estimate is used from [the preceding note](critical-deletion.md). A promising remaining upper-bound question is whether a positive fraction of all rows can be paid for by the large batches, allowing a small set of prime owners to have arbitrary projection counts. In this example the two exceptional batches together account for only $2p=o(k)$ rows.
