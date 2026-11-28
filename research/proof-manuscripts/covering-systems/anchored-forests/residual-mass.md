# A square-root bound for residual prime alphabets

Codex (OpenAI), 27 November 2026. AI-authored written supplement on Erdős #1189.

How many labels at a prime must remain available for interactions among different primes to improve the leading reciprocal coefficient? The following bounds apply to the fresh-prime substitutions used in the [cycle construction](cycles.md), with arbitrary mixed supports, multiplicities and overlap within each block. They use only universal noncoverage of the ordinary rows on the new coordinates. In particular the estimates also hold when the number of holes varies with the assignment.

## Hypotheses and conclusions

Each block introduces distinct fresh prime coordinates, disjoint from those in every other block. A row specifies one forbidden tuple on a nonempty subset $I$ of the new coordinates. Its integer modulus is a multiple of $\prod_{p\in I}p$. All the actual integer moduli are distinct. A block has $p-d_p$ singleton-support rows at $p$, where $1\le d_p\le p$. The mixed rows have $|I|\ge2$. Assume that every assignment of the forbidden tuples leaves a hole in each ordinary block. This is automatic for a fresh-prime stage of an irreducible cover when the preceding rows can leave a single residue of their period and the dressings divide that period: align all dressings with that residue and a covering assignment on the stage would give a proper subcover. The disjointness condition concerns the primes introduced as coordinates. Previously used primes may recur freely in the integer dressings.

For the claims about actual irreducible covers, one may include a fixed initial system, ordinary higher prime positions (at most $p-1$ distinct multiples of $p^j$ at each position $j\ge2$), and a final full-period row or the ordinary terminal extension of the [forest manuscript](anchored.pdf) using $p$ distinct multiples of a fresh prime $p$. Each prime position is charged once. Ordinary first positions with $p-1$ rows have $d_p=1$. The bounds have constants uniform for a fixed envelope on $d_p$ and a fixed initial system. Write $S=\sum 1/n$, $k$ for the number of moduli, $X$ for their maximum, $L$ for their lcm, and $F(y)=\sum_{p\le y}(p-1)$.

1. If $d_p\le p^{1/2+o(1)}$ uniformly, then $S\le(1/2+o(1))\log k$. If $d_p\le\sqrt p$ outside a fixed finite set, then $S\le R_0(k)+O((\log\log k)^2)$. Here $R_0$ is the known zero-defect optimum. Ordinary constructions give the matching leading coefficient at every sufficiently large exact size.
2. Suppose $d_p\le C\sqrt p/(\log(ep))^B$, with $B>0$. If $B>1/2$, then $S\le\Phi(L)+O(1)\le R_0(k)+O(1)$, where $\Phi(L)=\sum_{p^j\mid L}H_{p-1}/p^j$ sums over all positive prime positions. At $B=1/2$ the additive upper error is $O(\log\log k)$, and at $0<B<1/2$ it is $O((\log k)^{1-2B})$.
3. Under the envelope in 2, $k\le F(\sqrt X)+O(X/(\log X)^{2B}+X^{7/8}+X^{2/3}\log X)$. Thus at $B>1/2$ the least largest modulus in the class is asymptotic to $k\log k$ when ordinary extensions are admitted. At $B=1/2$ it has order $k\log k$. The sharp asymptotic already holds for a uniform envelope $d_p=o(\sqrt{p/\log p})$. The known ordinary construction with $X\le(1+o(1))k\log k$ supplies the upper bound at every sufficiently large exact size. Constants or finitely many small primes can be accommodated so this construction belongs to the class.

The numerical thresholds are sufficient conditions. Their necessity for these bounds is open. A sequence in this model that improves the reciprocal coefficient by a fixed positive amount must exceed $p^{1/2+\delta}$ at unbounded primes for some fixed $\delta>0$. Whether a general irreducible cover has a decomposition with useful bounds on the $d_p$ is a separate question.

## Two finite inequalities

For a mixed row $e$ on support $I_e$, put $w_e=\prod_{p\in I_e}d_p^{-1}$. For any set $U$ of prime coordinates,
$$
 \sum_{e:I_e\subset U}w_e\le\sum_{p\in U}\log d_p. \tag{1}
$$
Place the unary rows to leave exactly $d_p$ labels. Choose each indexed mixed row's forbidden tuple independently and uniformly on its residual support. On $U$ the expected number of survivors is exactly $\prod_{p\in U}d_p\prod_{e:I_e\subset U}(1-w_e)$. Every labeling leaves at least one survivor, since even the subsystem on $U$ cannot cover. Disjoint blocks combine by taking their product. The expectation is at least one, and $1-w\le\exp(-w)$ gives (1). This is the heterogeneous version of the usual first-moment bound in single-conflict colouring. See [Dvořák, Esperet, Kang and Ozeki](https://arxiv.org/abs/1803.10962) and the [hypergraph treatment](https://liu.diva-portal.org/smash/get/diva2%3A1973265/FULLTEXT01.pdf).

Assign a mixed row to the largest prime $q$ of its new support, and write its actual modulus $qm$. Assign a unary row to its only new prime. Let $S_q$ be the reciprocal mass thus assigned. Distinct integer moduli ensure distinct positive cofactors $m$ within this group. Then
$$
 S_q\le {H_{q-1}\over q}-{d_q-1\over q^2}
       +\sum_{e\ {\rm mixed\ at}\ q}{1\over q\max(q,m_e)}. \tag{2}
$$
Indeed, the sum of the positive parts of $1/(qm)-1/q^2$ over distinct $m$ is at most $H_{q-1}/q-(q-1)/q^2$. What remains from each unary row is at most $1/q^2$, and the remainder from each mixed row is exactly the summand on the right. This truncation pays for cheap mixed rows that would otherwise be charged at their full mass.

## Bounds on the remaining mass

In a dyadic band $Q\le q<2Q$, (1) and Chebyshev's estimate give $\sum_e w_e\le\sum_{p<2Q}\log p=O(Q)$. If $d_p\le p^\theta$ except at finitely many primes, $1/w_e\le C_\theta(qm)^\theta$ because each exceptional prime occurs at most once within a support. For any $\eta>0$, take $1/2<\theta<(1+\eta)/(2+\eta)$. The total contribution in (2) from $m>q^{1+\eta}$ in the band is
$$
 O_\eta\big(Q^{1-(2+\eta)(1-\theta)}\big).
$$
It is summable over dyadic $Q$. At a given $q$ the distinct smaller cofactors contribute at most $(1+\eta\log q+O(1))/q$, by using $1/q^2$ through $q$ and a harmonic sum thereafter. All prime divisors of an irreducible cover are at most $k$: at a hole of the rows below the top $p$-digit one needs at least $p$ rows carrying that digit. Thus $\sum 1/q=O(\log\log k)$ and $\sum (\log q)/q=O(\log k)$. Letting $\eta\downarrow0$ bounds the mixed error by $o(\log k)$ for the uniform subpower correction in 1.

If $d_p\le\sqrt p$ eventually, split instead at $m=q(\log(eq))^4$. Above the split each summand divided by $w_e$ is $O(1/[Q(\log Q)^2])$, giving a summable band error. Below it the bound at $q$ is $O((1+\log\log(eq))/q)$. Partial summation gives the stated squared logarithmic error.

Under hypothesis 2 define $D(J)=\prod_{p\in J}d_p$. For a finite set of primes $J$ whose product divides $v$,
$$
 D(J)\ll_{B,C}{\sqrt v\over(\log(ev))^B}. \tag{3}
$$
For large $p$, $d_p/\sqrt p\le(1+c\log p)^{-B}$ for a sufficiently small fixed $c>0$. Finitely many exceptions cost a single fixed factor. The product of $1+c\log p$ is at least $1+c\log(\prod p)$. Increasing $\prod p$ to $v$ changes the bound by at most a fixed factor since $\sqrt v/(\log(ev))^B$ is eventually increasing. Apply (3) separately to $q$ and to the other support primes, whose product divides $m$. For $m\ge Q^{1/2}$, the summand of (2) divided by $w_e$ is at most
$$
 O\left({1\over Q(\log Q)^{2B}}\right)
$$
using $\sqrt{qm}\le\max(q,m)$. For $m<Q^{1/2}$ it is $O(Q^{-5/4})$ directly. Multiply by the $O(Q)$ weight bound. Summing the resulting $(\log Q)^{-2B}+Q^{-1/4}$ over dyadic bands proves 2. Ordinary higher positions contribute at most their individual harmonic allowances by distinctness. A singleton costs at most one, and an ordinary terminal costs at most $H_p/p$. The uniform inequality $\Phi(L)\le R_0(k)+o(1)$ follows from the Znám–Simpson period bound and the [earlier first-position knapsack estimate](transfer.md).

## Counting at a cap

The top-digit argument needs $p$ distinct multiples of $p^{a}$ whenever $a=v_p(L)>0$, so $p^{a+1}\le X$. In particular all first-position primes are at most $\sqrt X$. Unary rows cost at most $F(\sqrt X)$ in total count. Ordinary higher positions contribute $O(X^{2/3}\log X)$: each has $p\le X^{1/3}$ and there are at most $\log_2 X$ positions per prime. A terminal adds at most one above its allowance.

For mixed rows with $q<X^{1/4}$, (1) bounds their total weight by $O(X^{1/4})$ and (3) bounds $1/w_e$ by $O(\sqrt X)$. This gives $O(X^{3/4})$ rows. For $m<X^{1/4}$ one has $qm\le X^{3/4}$, whence $1/w_e=O(X^{3/8})$, and all weights total $O(\sqrt X)$. For the remaining rows both $q,m\ge X^{1/4}$, so (3) twice gives $1/w_e=O(\sqrt X/(\log X)^{2B})$. This proves the count. With a uniform little-oh envelope at $B=1/2$, the bound for $d_q$ in this last range has an additional uniform $o(1)$ factor. Finally $F(\sqrt X)\sim X/\log X$ by the prime number theorem. Inverting the upper count proves the assertions about the cap without any monotonicity assumption on the minimum at exact size $k$.

The [finite check](residual-mass-check.py) evaluates the product inequality preceding (1) on every induced coordinate set for small heterogeneous grids, permitting repeated supports and triples. It independently checks (2) using exact fractions. The asymptotic bounds and their application to irreducible covers are written proofs.
