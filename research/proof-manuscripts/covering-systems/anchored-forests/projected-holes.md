# Many earlier holes survive erasure of prime coordinates

Codex (OpenAI), 27 November 2026. AI-authored written proof on Erdős #1189.

Let $D$ be an irreducible covering set of $k$ distinct moduli and $S=\sum_{n\in D}1/n$. The possible residue assignments are unrestricted. Suppose $S\ge(1/2+\epsilon)\log k$ for fixed $\epsilon>0$. The following necessary condition concerns the residues left uncovered by earlier moduli, even if they are assigned anew at each step.

**Erasure theorem.** For sufficiently large $k$ there are constants $\delta,c>0$ depending only on $\epsilon$ and a set of primes $k^\delta<p\le k$ of total reciprocal mass at least $c$ with this property. Reserve any one modulus before selecting the primes. At each selected $p$, take the earlier unreserved rows, those whose prime factors are all strictly less than $p$, and assign their residues in **any** manner. Start with all smaller primes dividing $L=\operatorname{lcm}D$ and erase **any** at most $k^c$ of them. The old holes project to at least $k^c$ different residue vectors on the retained primes, using just the residue modulo each prime. In particular there are at least $c k^\delta$ such prime positions. Each selected position also has $\sum_c 1/c\ge H_{p-1}+c\log k$, summed over the unreserved rows $pc$ with largest prime $p$ and $p\nmid c$.

This is a condition on all assignments of the same earlier rows. A large graph of prime divisors alone gives no such conclusion. The sharp unrestricted coefficient is still open.

## A finite capacity bound that pays for poorly separating rows together

Use any order on the prime-power positions of $L$ that respects powers of an individual prime. Reserve a row $n_*$. When the old period $K$ grows to $pK$, set $j=1+v_p(K)$ and $K'=K/p^{j-1}$. The rows first available at this position, excluding the reserved row, have the form $p^j c$ with distinct $c\mid K'$. Write $W=\sum_c1/c$. Give the earlier rows any residues and let $H$ be their nonempty set of holes modulo $K$.

Choose **any** divisor $g\mid K'$, let $b=|H\bmod g|$ and $P=p^j b$. Group cofactors by $v=c/\gcd(c,g)$. If $m_v$ is the number of rows in a group, then
$$
                        m_v<Pv. \tag{1}
$$
Indeed $c\mid gv$ throughout the group, and $gv\mid K'$ for an attained $v$. Every row in the group can test an old residue modulo $p^{j-1}c$ and one new $p$ digit. The old holes occupy at most $p^{j-1}bv$ joint residues modulo $p^{j-1}gv$. There are at most $Pv$ pairs of such residues and a new digit. If the group had $Pv$ rows, assign one distinct row to each pair, using the residue of any representative of that pair. Every lift in that pair is covered. Together with the earlier rows this would cover after deletion of $n_*$. This proves (1) independently for every group and for freely reassigned earlier rows. In particular the cofactors need not separate individual old holes.

**Position estimate.** Let $s$ be the number of primes dividing $K'$ that do not divide $g$. Higher powers missing from $g$ may be arbitrary. With an absolute constant,
$$
                      W\le H_{p^j-1}+\log b+O(1+\log(2+s)). \tag{2}
$$
To prove this, cofactors $c\le P$ cost at most $H_P$. For $i\ge0$ take the shell $2^i P<c\le 2^{i+1}P$ and $y=2^{i/3}$. The count with $v\le y$ is at most $P\sum_{v\le y}v\le Py^2$ by (1), so their total shell mass is at most $2^{-i/3}$. For larger $v$, use the distribution of missing prime powers in ordinary integers. For $r\mid K'$ put $a_r=v_r(g)$ and define
$$
 Z(n)=\sum_{r\mid K'} (\log r)\sum_{e>a_r}{\bf1}_{r^e\mid n}.
$$
For $c\mid K'$ this is exactly $\log(c/\gcd(c,g))$. In the uniform distribution on $1,\ldots,X$, for any integer $X\ge1$, divisibility by $d$ has probability at most $1/d$. Expanding the square and using coprimality across distinct primes gives
$$
 \mathbb E Z^2\le
 \left(\sum_{r\mid K'}\frac{\log r}{r^{a_r}(r-1)}\right)^2+
 \sum_{r\mid K'}\frac{(r+1)(\log r)^2}{r^{a_r}(r-1)^2}.
$$
The diagonal bound follows by summing $r^{-\max(e,f)}$ for $e,f>a_r$. The primes already present in $g$ contribute a bounded amount to each sum by comparison with $\sum_{n\ge2}(\log n)^2/n^2$. For the $s$ missing primes, the first sum is $O(1+\log(2+s))$ and the second $O(1+\log^2(2+s))$. Indeed the summands decrease eventually, so it suffices to take the first $s$ primes up to fixed adjustments. Partial summation with the prime number theorem gives these bounds. Thus the second moment is $O((1+\log(2+s))^2)$ uniformly in the exponents and $X$.

For $i\ge1$ take $X=2^{i+1}P$ and use the second-moment bound to count $Z(c)>i\log(2)/3$. These cofactors cost $O(\min(1,(1+\log(2+s))^2/i^2))$ in the shell. The zeroth shell costs at most one. Summation in $i$ gives $O(1+\log(2+s))$. Finally $H_P-H_{p^j-1}\le1+\log b$, proving (2). This estimates the combined cost of all the poorly separating rows using the arithmetic of their actual cofactors.

## Deriving the erasure theorem

Order the positions by prime, taking all powers of a prime before the next prime. Let $W_p$ be the first-position mass $W$ at $p$. All prime divisors of $L$ are at most $k$ by the highest-digit argument for irreducible covers. The mass of all positive integers whose largest prime occurs to exponent at least two is absolutely bounded, since
$$
  \sum_p\frac1{p(p-1)}\prod_{r<p}(1-1/r)^{-1}<\infty .
$$
Here and below the Euler product over primes through $z$ is $O(\log(ez))$ by Mertens' theorem. In particular the mass of all moduli supported on primes at most $k^\delta$ is $O(1+\delta\log k)$. The reserved row costs at most $1/2$. The [Znám–Simpson budget and harmonic knapsack estimate](transfer.md) imply $\sum_{p\mid L}H_{p-1}/p\le R_0(k)+o(1)=(1/2+o(1))\log k$. Choosing $\delta>0$ sufficiently small in terms of $\epsilon$ gives, for large $k$,
$$
 \sum_{k^\delta<p\le k,\ p\mid L}\frac{(W_p-H_{p-1})_+}{p}\ge \tfrac12\epsilon\log k.
$$
The sum of $1/p$ in this interval is bounded in terms of $\delta$. Positions with surplus below $\eta\log k$ therefore contribute at most $\epsilon\log k/4$ for some $\eta>0$. Each other position has surplus at most $H_k\le1+\log k$ by distinctness of its at most $k$ cofactors. The latter primes consequently have total reciprocal mass at least a positive constant depending only on $\epsilon$.

At each of these primes choose $g$ to be the product of all earlier primes except an arbitrary erased set of size at most $k^c$. The quantity $b$ counts exactly the joint residues in the assertion. By (2), $\eta\log k\le\log b + C(1+\log(2+k^c))$. Choosing $c$ sufficiently small forces $b\ge k^c$. Decrease $c$ further to cover the reciprocal-mass and surplus assertions. Nothing in the selection of the primes used the assignments or the erased sets.

Small disjoint sets of coordinates can witness this conclusion at many different primes. Reduce $c$ to at most $\delta$ if necessary, put $m=\lfloor k^{c/3}\rfloor$, select $m$ of the good primes and give each its own arbitrary assignment of earlier rows. At each step erase the selected primes and all witness coordinates used at earlier steps, in so far as they are earlier primes for this step. Fewer than $m+m^2\le k^c$ coordinates are erased for large $k$. Among $m$ distinct patterns on the remaining coordinates, at most $m-1$ coordinates distinguish all $m$: while two patterns still agree on the chosen coordinates, include one coordinate on which they differ. The number of distinct restrictions increases each time. Thus there are $m$ pairwise disjoint panels of at most $m-1$ old primes, disjoint also from the selected primes, each detecting at least $m$ patterns of its assigned holes. The panels may depend on the assignments.

## A bounded additive estimate for moving holes

There is a complementary estimate when a few primes account for all the variation. At a prime position choose $g$ for which $b=1$. Suppose all but at most $s_0$ primes of $K'$ occur in $g$ to their full old exponent, with fixed $s_0$. Write $J$ for the exceptional primes. If $r\in J$, put $z_r=r^{v_r(g)+1}$. Then
$$
               W\le H_{p^j-1}+
                    O_{s_0}\left(\sum_{r\in J}\frac{1+\log z_r}{z_r}\right). \tag{3}
$$
The $v=1$ group has at most $P-1$ members, with $P=p^j$. Summing $(1/c-1/P)_+$ over all distinct cofactors costs at most $H_{P-1}-(P-1)/P$. Thus only $\sum1/\max(P,c)$ from groups $v>1$ remains. Write $z(v)=v\prod_{r\mid v}r^{v_r(g)}$. Every member of the $v$ group is divisible by $z(v)$. By (1) its clipped mass is at most the sum over the first $Pv$ multiples of $z(v)$, clipped at $1/P$. Separating at $P/z(v)$ and summing the harmonic tail bounds this by $(2+\log(2v z(v)))/z(v)$, also when $P<z(v)$. Sum over all nontrivial $J$-smooth $v$. For each $r$ the positive exponents give $z(r^a)=z_r r^{a-1}$, with $\sum_{a\ge1}1/z(r^a)\le2/z_r$ and $\sum_{a\ge1}\log z(r^a)/z(r^a)\ll(1+\log z_r)/z_r$. Since $v\le z(v)$, expanding the product over at most $s_0$ primes proves (3).

For example suppose these choices exist at each first position, and each old varying prime $r$ occurs in $J$ at only boundedly many first positions. The total first-position surplus is bounded: use $(1+\log z_r)/z_r\le (1+\log r)/r$ and Cauchy–Schwarz over the pairs $(p,r)$, since both degrees are bounded and $1/p$ and $(1+\log r)/r$ are square summable over primes. Under the increasing-prime order the contribution with largest prime squared is already bounded. This gives $S\le\Phi(L)+O(1)$ for this class. It allows arbitrarily many old holes and arbitrary powers at the varying primes. Persistent reuse of the same small prime is outside this corollary.

## The largest modulus under the same projection mechanism

Suppose at every prime position one can choose $g$ with $b\le b_0$ and at most $s_0$ primes of $K'$ missing any of their old powers, where $b_0,s_0$ are fixed. For $M=\max D$ we have
$$
                              k=O_{b_0,s_0}(M/\log M).
$$
If in addition $b=1$ at first positions and every exceptional prime power $z_r$ at such a position satisfies $z_r/\log p\to\infty$ uniformly as $p\to\infty$, then
$$
                    k\le(1+o(1))M/\log M .
$$
In the [earlier every-size construction](../reciprocal-sums/reciprocal.tex), reserve one terminal row. In its specified order the first nonzero old digit covers every old point except zero before each step. Thus one may take $g=K'$ and $b=1$ throughout. That construction gives $M\le(1+o(1))k\log k$ at every sufficiently large exact size. Hence the latter estimate yields the sharp minimum in the indicated class.

**Proof.** In either case, the row count at one position is at most
$$
 \sum_{v\ J\text{-smooth}}\min\{p^j b v,M/(p^j v)\}
 \ll_{s_0}\sqrt{b M}\big(1+\log^+(\sqrt{M/b}/p^j)\big)^{s_0}.
$$
The second term inside the minimum uses divisibility by $v$. For the sum put $y=\sqrt{M/b}/p^j$. If $y\ge1$, there are $O_{s_0}((1+\log y)^{s_0})$ smooth integers up to $y$ by counting exponents. Group the larger integers in $(2^i y,2^{i+1}y]$ and use the geometric factor $2^{-i}$. When $y<1$, use $\sum_v1/v\le2^{s_0}$. There are $O(M^{1/3}\log M)$ higher positions since the top $p$ digit needs $p$ rows of distinct moduli divisible by its full power, giving $p^{v_p(L)+1}\le M$. Their combined count is $o(M/\log M)$. For first positions $p\le\sqrt M$. Summing the position estimate costs $O_{b_0,s_0}(M/\log M)$: primes up to $M^{1/4}$ contribute $O( M^{3/4}(1+\log M)^{s_0})$, and for larger primes dyadic intervals below $\sqrt M$ have geometrically decreasing counts $O(2^{-i}\sqrt M/\log M)$ and only polynomial growth in $i$ in the weight.

For the sharp constant, at first positions above $M^{1/4}$ the $v=1$ group has at most $p-1$ rows. Any other cofactor is divisible by some $z_r$ and hence there are at most $(M/p)\sum_{r\in J}1/z_r$ such rows. The threshold assumption makes their sum $o(M/\log M)$ since $\sum_{M^{1/4}<p\le\sqrt M}1/p=O(1)$. The prime number theorem gives $\sum_{p\le\sqrt M}(p-1)\sim M/\log M$. This is an exact-cardinality argument and requires no monotonicity of the minimum.

**Status and sources.** The general results are written proofs. The [exact finite tests](projected-holes-check.py) verified 40,240 projected cuts, including 25,514 with multiple projected holes, 102,901 nonempty cofactor groups, and 648 rational second-moment cases. The checks enumerate all earlier residue assignments in the period-12 example and two prescribed choices in the period-420 example. The asymptotic argument has not been formalized in Lean. The erasure condition is necessary. A remaining route is to rule out polynomially many such earlier residue patterns *at many large primes simultaneously*, or to construct an irreducible family exhibiting them with enough reciprocal mass.

[Original Erdős–Graham problem](https://www.erdosproblems.com/1189) · [Earlier prime-position sieve](prime-position-sieve.md) · [Unrestricted transfer and credits to Öztürk, Star Fleet Math and Wouter van Doorn](unrestricted-transfer.md) · [Mertens estimates](https://link.springer.com/article/10.1007/s11139-024-00893-8)
