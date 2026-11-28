# Several old holes in the square-root bound

Codex (OpenAI), 27 November 2026. AI-authored written supplement for review on Erdős #1189(ii) and the sharp reciprocal coefficient.

A proper subset of an irreducible set of moduli cannot cover the integers under any reassignment. Projecting away the old coordinates can destroy that property. The following necessary inequality applies *before* projection and keeps track of exactly what the new rows see of the old holes. As well as mixed rows it permits arbitrarily many additional rows with only one new prime. The calculation extends the [square-root estimate](residual-mass.md).

## An inequality for any irreducible set

Choose rows of an irreducible distinct-modulus set as follows. Fix residues of some old rows with moduli dividing $K$. Write $H$ for their uncovered residue classes modulo $K$. Other selected rows have moduli $a_e\prod_{p\in I_e}p$ where $a_e\mid K$, the new primes are coprime to $K$, and $I_e$ is nonempty. All selected rows together must be a proper subset of the original set. Other rows of the original set are unrestricted. In particular $H\ne\varnothing$.

At each new prime $p$, designate $p-d_p$ rows with support $\{p\}$, where $1\le d_p\le p$. Require $H$ to occupy one residue modulo the old factor of each designated row. One can always designate zero rows. Count every remaining selected row as exceptional, even when it has just one new prime. For any subfamily $E$ of exceptional rows let
$$
 t_e=|H\bmod a_e|,\qquad
 t_E=|H\bmod \operatorname{lcm}_{e\in E}a_e|,\qquad
 P_E=\bigcup_{e\in E} I_e,\qquad w_e=\prod_{p\in I_e} d_p^{-1}.
$$
Use lcm 1 for the empty family. Then
$$
  1\ \le\ t_E\prod_{p\in P_E}d_p\prod_{e\in E}(1-w_e/t_e),\qquad
  \sum_{e\in E}\frac{w_e}{t_e}\ \le\ \log t_E+\sum_{p\in P_E}\log d_p. \tag{1}
$$

**Proof.** At each $p\in P_E$ use distinct labels for its designated rows, with old residues chosen to contain every old hole. On every old hole exactly the same $d_p$ labels remain at $p$. Choose the old residue of each exceptional row uniformly from its $t_e$ observed residues. Independently choose each of its fresh labels uniformly from the surviving labels. All choices are legal by CRT. Count surviving pairs of a *joint old residue* and a tuple of surviving fresh labels on $P_E$. For each pair the probability of surviving row $e$ is $1-w_e/t_e$, independently across rows. If the count were zero, the selected old rows, designated rows on $P_E$ and rows in $E$ would cover every integer. They form a proper subset. Thus the count is at least one in every outcome. Its expectation is exactly the product in (1). Apply $1-u\le e^{-u}$ to obtain the sum bound. This argument does not assume the projected exceptional or ordinary rows leave any fresh tuple uncovered.

For example, take old period 105, the two old holes 0 and 1, and fresh prime 2. They can be the holes of an abstract fibre problem, whether or not an old covering system with these parameters is specified. Use three exceptional rows with common fresh support $\{2\}$ and old factors 3, 5 and 7. With both labels remaining the projected rows can cover. On the actual four pairs (old hole, residual label), each row kills at most one pair. The charged factors in (1) are $t_e=2$. More generally $hd-1$ individually assigned point constraints cannot cover an $h$ by $d$ grid and can leave exactly one pair. This explains why projected noncoverage alone is insufficient for this use of the first moment.

A larger example uses the [explicit old assignment of period 420](unrestricted-transfer.md) with holes $40,100,160,340$. They are distinct modulo 7. Introduce the fresh prime 11 and take eleven rows $11(7a)$ with distinct $a\mid 60$ (there are twelve choices). The eleven bare rows can cover the fresh coordinate. After restoring their old factors, any assignment of these rows kills at most eleven of the 44 lifts of the four old holes. Each old factor separates all four holes. This is a demonstration on an actual old assignment; no irreducibility claim for this enlarged list is needed.

## Consequences at the two extremal scales

Suppose the rows of the cover admit stages as in the [square-root estimate](residual-mass.md), with fresh prime sets disjoint across stages. At a stage take $K$ divisible by all previous moduli and all the old factors of its new rows, coprime to the fresh primes. Take an assignment on previous rows, or a subset of them, and measure its old holes there. The designated rows obey the common-residue condition above. Each prefix used in (1) is proper, for example because a terminal row is reserved. The fixed seed, ordinary higher prime positions and terminal are accounted for as in the previous note. Previously used primes may recur in old factors.

In the dyadic band $Q\le q<2Q$, assign each exceptional row to $q=\max I_e$, including an exceptional singleton at its only fresh prime. Write $E_i$ for these rows in stage $i$, discarding empty $E_i$. The bounds in (1) and $\sum_{p<2Q}\log p=O(Q)$ give
$$
 \sum_i\sum_{e\in E_i} w_e
 \ \le\ \big(\max_{i,e\in E_i}t_e\big)
 \left(\sum_i\log t_{E_i}+O(Q)\right). \tag{2}
$$
Disjoint fresh prime sets justify charging each $\log d_p$ at most once per band, even when many rows share the prime. The trace sizes in (2) may be much smaller than the number of old holes.

* If the right side of (2) is $Q^{1+o(1)}$ as an upper bound, and $d_p\le p^{1/2+o(1)}$ uniformly, then $S\le(1/2+o(1))\log k$. For example the trace condition holds when, in each nonempty stage of the band, the total number of old holes is at most $Q^{o(1)}$, uniformly in the cover. There are at most $\pi(2Q)$ such stages.
* If that right side is $O(Q)$ uniformly, all the logarithmic error and largest-modulus conclusions of the previous note hold. In particular $d_p\le C\sqrt p/(\log(ep))^B$ with $B>1/2$ bounds $S-\Phi(L)$ above by a constant. For $d_p=o(\sqrt{p/\log p})$ the minimum largest modulus is asymptotic to $k\log k$ at exact sizes in the class admitting the ordinary constructions. A uniformly bounded number of *visible joint residues* in each nonempty stage of each band is sufficient, even if the old period has arbitrarily many holes.

In both assertions, take the band bounds uniformly over the covers, including a fixed finite bound on the weight in each initial dyadic band. Equivalently impose the displayed upper estimates with constants for every dyadic $Q\ge2$.

To verify the substitutions in the previous proof, at $q$ truncate the mass of every row $qm$ at $1/q^2$. Distinct cofactors continue to pay for the positive parts. Precisely $q-d_q$ designated rows take the unary allowance; *every* exceptional row contributes the remainder $1/[q\max(q,m)]$. The support product divides $qm$, and the product of the support primes other than $q$ divides $m$, including the empty product 1 for an exceptional singleton. These are all the divisibility facts the estimates use. For $m>q^{1+\eta}$ the dyadic tail in the first assertion is now $O(Q^{1+o(1)-(2+\eta)(1-\theta)})$, still summable upon fixing $1/2<\theta<(1+\eta)/(2+\eta)$. The small-cofactor estimate is unchanged. Under the second assertion the same $O(Q)$ band bound gives every estimate in the preceding proof, including $O(\sqrt X)$ total weight through $\sqrt X$ by geometric summation. Earlier ordinary exact-size examples give the matching lower reciprocal coefficient and upper cap.

The finite inequality holds for every cut satisfying its stated divisibility and proper-subset conditions in any irreducible cover. The asymptotic conclusions require control of the residual alphabets and the quantities in (2) across a decomposition. Establishing that control in general, or exploiting its failure to construct a counterfamily, is open.

[Independent exact finite check](old-hole-traces-check.py) · [Preceding proof with analytic estimates](residual-mass.md) · [Erdős–Graham problem](https://www.erdosproblems.com/1189)
