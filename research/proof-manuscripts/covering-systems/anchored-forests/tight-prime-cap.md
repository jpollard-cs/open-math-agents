# The sharp size at a modulus cap with one nontight prime

Codex (OpenAI), 28 November 2026. AI-authored written asymptotic proof for public review.

Let $K_1(X)$ be the largest cardinality of an irreducible set of distinct moduli in $[2,X]$ for which all but at most one prime in the period satisfy $W_p=1$, with $W_p$ as in [the elimination theorem](tight-prime-forests.md). Write $L=\log X$ and $A=L/\log2$. Then
$$ K_1(X)\sim\frac{\pi^2}{36}\frac{A^2 L}{(\log A)^2}. $$
Earlier [prime-separator work](../prime-separators/prime-separators.md) obtained order bounds and constructions with a fixed set of prime hubs. Here rows may involve many tight primes together. The equality constraints and arbitrary-reassignment irreducibility determine the leading constant. This is a maximum size at a given cap, with no assertion that intermediate sizes are all attained.

**Upper bound.** Select all primes except the possible exception $r$ as $P$, and use the forest theorem. A row containing at least two primes of $P$ will be called mixed here. If $E_p$ counts incidences with such rows at $p$, then
$$ \sum_{p\in P}E_p\le2|P|. $$
Indeed the sum of $(\deg(n)-1)$ across all row vertices is $|P|$ minus the number of components. The mixed-row degree is at most twice its contribution to that sum. A row using $p$ but no other prime of $P$ has shape $p^j r^b$. For singleton rows at exact $p$-valuation $j$ the upper bound is
$$ b_j=\max(0,1+\lfloor A-j\log_2 p\rfloor) $$
for each depth. Including all rows, the count satisfies $t_j\le b_j+E_{p,j}$, with $\sum_j E_{p,j}=E_p$. There are no rows at $j>J=L/\log p$. From $W_p=1$ we get $1\le(A+1)/(p-1)+E_p/p$, hence $p\le A+2+E_p$. Primes $p>2A+4$ each require more than $A$ mixed incidences, so $|P|\le\pi(2A+4)+2|P|/A$. Therefore $|P|=O(A/\log A)$, and uniformly $E_p=o(A)$ and $p\le(1+o(1))A$.

Let $h_0=1$ and $h_j=p h_{j-1}-t_j$. The exact length equality says $h_j=\sum_{s\ge1}t_{j+s}/p^s$. These are nonnegative integers, eventually zero. Since $b_j$ is nonincreasing,
$$ h_j\le \left\lfloor\frac{b_{j+1}+E_p}{p-1}\right\rfloor,\qquad
 \sum_{j\ge1}t_j=p+(p-1)\sum_{j\ge1}h_j. $$
On any fixed band $\epsilon A\le p\le(1+o(1))A$ put $u=p/A$. Uniformly there, summing these bounds gives
$$ \sum_jt_j\le pJ\big(I(u)+o_\epsilon(1)\big),\qquad
 I(u)=\int_0^1\left\lfloor\frac{1-s}{u}\right\rfloor ds
      =\sum_{i\ge1}(1-iu)_+. $$
To see uniformity, the argument inside each floor differs from $(1-j/J)/u$ by $o_\epsilon(1)$ over $1\le j\le J$ before flooring. The number of discontinuity levels is $O_\epsilon(1)$. The fraction of mesh points within $\eta$ of these levels is $O_\epsilon(\eta+1/J)$; also $J\to\infty$. This proves the estimate up to both endpoints.

For $p\le\epsilon A$ one has $\sum_jt_j\le (A+1)L/\log p+E_p$. By the prime number theorem $\sum_{p\le z}1/\log p=O(z/(\log z)^2)$, so this range contributes at most $O(\epsilon) A^2 L/(\log A)^2$ in the limit for fixed $\epsilon$. Pure powers of $r$ contribute $O(L)$ more. Sum the band estimate over all primes in that band, using the prime number theorem on fixed proportional intervals and continuity of $uI(u)$ on $[\epsilon,1]$. Then let $\epsilon\downarrow0$. The upper constant is
$$ \int_0^1 u I(u)\,du=\sum_{i\ge1}\int_0^{1/i} u(1-iu)\,du
   =\tfrac16\sum_{i\ge1}i^{-2}=\pi^2/36 . $$

**Attainment.** Fix $0<\epsilon<1/2$ and use $r=2$ and all primes $\epsilon A\le p\le(1-\epsilon)A$. Assign each such prime a different integer $B_p=A-o(A)$, with $B_p\le A-2\log_2 A$; there is room since there are $O(A/\log A)$ primes. For that prime set
$$ c_j=\min(B_p+1,b_j),\qquad h_0=1,\qquad
 h_j=\lfloor c_{j+1}/p\rfloor\ (j\ge1),\qquad t_j=p h_{j-1}-h_j . $$
For large $A$, $0\le t_1\le c_1$ and $t_1>0$, because $p\le(1-\epsilon)A$ and $h_1=O_\epsilon(1)$. For $j\ge2$, monotonicity of $h$ from $h_1$ gives $0\le t_j\le p h_{j-1}\le c_j$. Each $h_j$ vanishes eventually, so $\sum_jt_j/p^j=1$. At depth $j$ take $t_j$ distinct row moduli $2^b p^j\le X$ with $0\le b\le B_p$. At the first depth include $2^{B_p}p$. The component is a tree with one prime vertex, contracting exactly to $2^{B_p}$. The same mesh estimate now gives equality $\sum_jt_j=pJ(I(u)+o_\epsilon(1))$, since the cap $B_p$ changes the rescaled argument by only $o_\epsilon(1)$.

Let $B=\max B_p$. The virtual binary list with one copy of each $2,4,\ldots,2^B$ and one extra copy of $2^B$ has reciprocal sum one. Replace one row of each selected depth $B_p$ by the component just described. All actual moduli are distinct, since the first copy of $2^B$ was replaced and different components use different primes. All moduli obey the cap, and the contraction theorem proves that every row is necessary even after reassigning all other residues. Summing over $[\epsilon A,(1-\epsilon)A]$ gives the integral on that interval. Taking $\epsilon\downarrow0$ proves the matching lower constant.

[Finite tests of tree contraction and the integer frontier bounds](tight-prime-check.py). For the unrestricted problem the forest certificate uses an exclusive residue at each prime on a proposed cycle. Once every such residue has other owners, the fixed-value deletion breaks down. One direction is to bound the reciprocal cost of all possible alternate owners in a cycle and allow a small number of those rows to survive. The full unrestricted minimum and reciprocal coefficient remain undecided by this result.

## Stability under overlapping projections

The same leading upper constant holds far beyond equality. In a covering assignment, count an incidence $(p,n)$ as bad if $p\mid n$ but the full $p$-projection of row $n$ has no value exclusive to that row among all rows testing $p$. Ignore an arbitrary one prime $r$. If the total number $D$ of bad incidences at the remaining primes is $o(A^2/\log A)$, then the same asymptotic **upper** bound holds for the size. Tight constructions above attain it. It is enough that a single covering assignment satisfies this bound; the moduli themselves must still be freely irreducible.

To see this, remove the bad edges: the exclusive edges form a forest by the elimination theorem. In the full graph the sum over row vertices of $(\deg-1)$ is therefore at most $|P|+D$, since adding an edge increases this sum by at most one (isolated vertices may be retained). Consequently $\sum E_p\le2(|P|+D)$. All axis projections together cover each $p$-axis. Their residue classes form a laminar family, so choose the maximal classes with one representative each. These are a partition. Every discarded indexed incidence was bad. Let $t'_j$ count the retained cells at $p$ and depth $j$. They have length sum exactly one. Over all primes, replacing $t_j$ by $t'_j$ loses at most $D$ incidences. These are only local selections for an upper bound, with no requirement of a common row selection at different primes.

Since $W_p\ge1$, still $p\le A+2+E_p$. Therefore $|P|\le\pi(2A+4)+2(|P|+D)/A=O(A/\log A)$. Choose a positive $\delta_A\to0$ slowly enough that $(|P|+D)/(\delta_A A)=o(A/\log A)$. Only $o(A/\log A)$ primes have $E_p>\delta_A A$. For fixed $\epsilon>0$ those exceptional primes with $p\ge\epsilon A$ contribute $o(A^2L/(\log A)^2)$ singleton rows by the bound $(A+1)L/\log p$ per prime. All mixed incidences together are negligible on this scale as well. The small-prime bound from the main proof is unchanged. At every other prime use the same floor bound on the partition counts $t'_j$, since $E_p=o(A)$ uniformly and $p\le(1+o(1))A$. This proves the assertion. A sufficient assignment-independent condition is
$$ \sum_{p\ne r}p^{v_p(\mathrm{lcm}(D_{\rm rows}))}(W_p-1)=o(A^2/\log A). $$
Indeed, on a coordinate value of multiplicity $h\ge2$, at most $h\le2(h-1)$ row incidences overlap; other coordinate values contain no bad incidences. Each bad incidence has length at least one full coordinate cell. Summing gives the required bound with factor two.

At the unrestricted scale a direct count gives a further necessary condition. For any covering assignment of an irreducible list at cap $X$, the total number of exclusive incidences, counting every prime, is at most $F(\sqrt X)+o(X/\log X)$ where $F(y)=\sum_{p\le y}(p-1)$. Each period prime has $p\le\sqrt X$, since at least $p$ distinct multiples must test it. At exponent one there are at most $p$ exclusive incidences per prime. For $p>(\log X)^2$ the number of higher-exponent incidences is bounded by $X\sum_{n>(\log X)^2}1/n^2=o(X/\log X)$. At the smaller primes, each exponent $j$ supplies at most $\min(p^j,X/p^j)\le\sqrt X$ exclusive rows and there are $O(\log X)$ exponents. Thus any fixed-factor violation $k\ge F(\sqrt X)+cX/\log X$ forces at least $(c-o(1))X/\log X$ original rows with **no exclusive coordinate at any prime**, in every covering assignment.
