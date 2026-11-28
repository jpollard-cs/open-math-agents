# Counting progression-free subsets at almost every logarithmic scale

Research draft · November 26, 2026. Written by OpenAI Codex with collaborating AI agents.

For a fixed integer $k\ge3$, let $r_k(n)$ be the maximum size of a subset of $[n]=\{1,\ldots,n\}$ containing no nonconstant $k$-term arithmetic progression. Let $I_k(n)$ be the number of all such subsets, including the empty set. Every subset of one maximum set is progression-free, so $I_k(n)\ge 2^{r_k(n)}$. The question is whether this explains the leading exponent of the count.

**Theorem 1.** Write $\alpha=1/\lceil\log_2 k\rceil$. As $X\to\infty$,
$$
0\le \frac{1}{\log X}\sum_{n\le X}\frac{1}{n}
\left(\frac{\log_2 I_k(n)}{r_k(n)}-1\right)
\ll_k \frac{\log\log X}{(\log X)^{1-\alpha}}.
$$
For each fixed $k$, there is a set of integers $G_k$ of logarithmic density one along which $\log_2 I_k(n)=(1+o(1))r_k(n)$. In particular, this holds for $k=3$ and $k=4$, in both cases with mean excess $O(\log\log X/\sqrt{\log X})$.

Morris, Ortega and Rué established the sharp exponent along an infinite sequence for $k\ge5$ and an upper bound $2^{O_k(r_k(n))}$ at all lengths for $k\ge3$. Their Question 7.1 asks about $k=3,4$ and separately about all lengths. Theorem 1 gives an affirmative answer to the first clause for arithmetic progressions. The all-length counting question and the extremal asymptotic in Erdős Problem #142 both remain open. The proof has received internal AI checks. Independent mathematical review is invited. No priority or formal-verification claim is made. [Morris, Ortega and Rué, §§1 and 7](https://arxiv.org/abs/2607.17746) · [Erdős Problem #142](https://www.erdosproblems.com/142)

## Two inputs from the literature

Write $r=r_k(n)$ and $\rho(m)=r_k(m)/m$. All unmarked logarithms are natural. Constants may depend on $k$. The Behrend–Rankin lower bound gives a constant $C_k$ with
$$
r_k(m)\ge m\exp\{-C_k(\log(em))^\alpha\}\qquad(m\ge1).
$$
The AP hypergraph on a set $V\subseteq[n]$ has vertex set $V$ and one edge for each $k$-term progression in $V$. Its independent sets are precisely the progression-free subsets. [Morris, Ortega and Rué, equation (2)](https://arxiv.org/abs/2607.17746)

A cover of a hypergraph is a family $\mathcal D$ such that every hypergraph edge contains some member of $\mathcal D$. Theorem A of Campos and Samotij, applied to this $k$-uniform hypergraph on $V$ and $0<q\le 1/(8k^2)$, gives a family of sets $B\subseteq V$ with three properties.

- Every independent set in $V$ lies entirely in some $B$.
- Each $B$ is determined by a fingerprint, a subset of $V$ of size at most $8k^2q|V|$. Thus for small $q$ the logarithm of the number of choices is $O_k(|V|q\log(e/q))$. This follows from the binomial sum and includes the case where only the empty fingerprint is possible.
- For each $B$, the AP hypergraph on $B$ has a cover $\mathcal D$ of sets of size at least two with $\sum_{S\in\mathcal D}q^{|S|}\le q|B|$. Discarding any members of size greater than $k$ preserves the cover. We call the remaining cover a cheap cover at parameter $q$.

The fingerprint bound uses $|V|$. The weight bound uses $|B|$. Both features matter when applying the theorem a second time inside a smaller set. [Campos and Samotij, Theorem A](https://arxiv.org/abs/2408.06617)

## 1. Stop the first stage early

For a sufficiently large scale $L$, the AP-free sets in $[n]$ have a covering family $\mathcal V$ with
$$
|V|\le 2Lr \quad(V\in\mathcal V),\qquad
\log_2|\mathcal V|\ll_k r/L. \tag{1}
$$
Here a covering family of sets means every AP-free set lies in a member. The members can contain progressions.

One route to (1) is the proof of Theorem 5.4 of Morris, Ortega and Rué. It starts at size $n$ and halves the scale $\lambda$ at each step. At scale $\lambda$ its members have size at most $\lambda r$. The increase in the logarithm of the family size is $O_k(r/\lambda)$ per step, by their equation (22). Stop at the first scale in $(L,2L]$. The sum of the costs is a geometric series bounded by $O_k(r/L)$. If $n\le 2Lr$, the single set $[n]$ suffices. The scale thresholds depend only on $k$ and its fixed extremal lower-bound constants. The appendix supplies a direct, stronger version of (1) specialized to progressions. [Morris, Ortega and Rué, proof of Theorem 5.4](https://arxiv.org/abs/2607.17746)

## 2. A grid estimate without boundary exceptions

Suppose $B\subseteq[n]$ admits a cheap cover at $q$. Let $1\le m\le n$, let $d\ge2$ be an integer, and let $\pi(d)$ denote the number of primes up to $d$. Put
$$
u=\frac{m}{n+dm},\qquad \theta=q^{1-k}\frac{\log_2 n}{\pi(d)}.
$$
Then
$$
r_k(m)\ \ge\ u|B|(1-\theta). \tag{2}
$$

Choose a prime $p\le d$ uniformly, choose an integer $b$ uniformly from $1-dm,\ldots,n$, independently, and let $J=b+p[m]$. Allowing the grid to extend outside $[n]$ makes every $x\in[n]$ equally likely to occur. For each fixed prime there are exactly $m$ admissible starts $x-pi$, $1\le i\le m$. Thus $\Pr(x\in J)=u$. For distinct $x,y\in[n]$, a prime step must divide $|x-y|$ for both to occur. The difference has at most $\log_2 n$ distinct prime divisors, and for each such prime there are at most $m$ admissible starts. Hence
$$
\Pr(x,y\in J)\le u\,\log_2 n/\pi(d).
$$

Each cover member has size between two and $k$, so there are at most $q^{1-k}|B|$ members and each is present with probability at most the displayed pair bound. From $B\cap J$ delete one point from every fully present cover member, counting a shared deletion only once. The remainder contains no progression and maps affinely to a subset of $[m]$. Its size is at most $r_k(m)$ in every outcome and its expected size is at least the right side of (2). This proves the estimate. The prime-step sampling idea also appears in the proof of Proposition 4.1 of Morris, Ortega and Rué. The padded range for $b$ gives (2) directly. [Morris, Ortega and Rué, §4](https://arxiv.org/abs/2607.17746)

## 3. Refine inside each first-stage set

Take $T$ a sufficiently large power of two, $T\le t<2T$ an integer, and $2^t\le n<2^{t+1}$. Define
$$
h=\lceil20k\log_2 T\rceil,\quad m=2^{t-h},\quad K=2^{t+h},
\quad L=T,\quad q=T^{-3}.
$$
For each $V$ from (1) apply the Campos–Samotij theorem to the induced hypergraph on $V$. Taken over all $V$, the resulting family $\mathcal B$ covers all AP-free sets in $[n]$. Its entropy satisfies
$$
\log_2|\mathcal B|\ll_k r/T + (Tr)q\log(e/q)\ll_k r/T. \tag{3}
$$
An edge lying in a final member $B\subseteq V$ is precisely an ambient AP lying in $B$. Its cheap cover from this application therefore satisfies (2).

Use $d=\lfloor\sqrt{n/m}\rfloor$. Then $d\asymp_k T^{10k}$, $dm/n\ll_k T^{-10k}$ and $\log n\ll T$. The elementary prime bound $\pi(d)\gg d/\log d$ gives
$$
\theta\ll_k T^{3(k-1)} T(\log T)T^{-10k}=o(T^{-1}).
$$
Solving (2) for $|B|$ gives, uniformly throughout the shell,
$$
|B|\le n\rho(m)(1+O_k(T^{-1})). \tag{4}
$$
The use of the small vertex set $V$ in (3) permits a polynomially small $q$. Consequently the factor $n/m$ in (4) is only a power of $\log n$. Paying the fingerprint cost on all $n$ vertices would lose precisely this advantage.

## 4. Count the exceptional lengths

Put $f(s)=\log(2^s/r_k(2^s))$ for integers $s\ge0$. Splitting an interval into halves proves $f$ is nondecreasing. Behrend–Rankin gives $0\le f(s)\ll_k (1+s)^\alpha$. Let
$$
D_t=f(t+h)-f(t-h)\ge0.
$$
Tiling $[K]$ by at most $\lceil K/n\rceil$ intervals of length at most $n$ gives
$$
\rho(m)=e^{D_t}\rho(K)\le e^{D_t}(1+n/K)\rho(n),
\qquad n/K\le 2^{1-h}.
$$
If $D_t\le1$, (3)–(4) bound $\log_2 I_k(n)$ by the maximum member size plus $\log_2|\mathcal B|$, and give
$$
E_k(n):=\frac{\log_2 I_k(n)}{r_k(n)}-1\ \ll_k\ D_t+T^{-1}. \tag{5}
$$
If $D_t>1$, (1) at a fixed sufficiently large $L$ gives $E_k(n)=O_k(1)$, so (5) still holds. Its nonnegativity follows from the subsets of a maximum independent set.

In the sum of the $D_t$ over $T\le t<2T$, each nonnegative increment of $f$ occurs at most $2h$ times. Therefore
$$
\sum_{T\le t<2T}D_t\le 2h f(2T+h)\ll_k T^\alpha\log T.
$$
Each shell has $\sum_{2^t\le n<2^{t+1}}1/n\le1$. Sum (5) over shells, then over the powers of two $T$ up to $\log_2 X$. The last block may be bounded by a complete block since the summands are nonnegative. The geometric sum is $O_k((\log X)^\alpha\log\log X)$, which proves Theorem 1.

For an explicit density-one set, keep the shells in each block where $D_t\le T^{\alpha-1}(\log T)^3$. At most $O_k(T/(\log T)^2)$ shells in that block are omitted. Thus $\sum_{n\le X,\,n\notin G_k}1/n=o(\log X)$, and (5) tends to zero on the retained lengths.

## Uniform control on shorter ranges

The same proof locates good lengths near any sufficiently large starting scale. Let $T$ now be any sufficiently large integer and $h=\lceil20k\log_2(2T)\rceil$. Use these common parameters on $T\le t<T+H$, where $h\le H\le T$ is an integer. The bounds (3)–(5) still apply as $t$ stays between $T$ and $2T$.

For $b>a\ge0$, the digit product proved in the appendix gives $r_k(2^b)\ge r_k(2^a)r_k(2^{b-a-1})$. Consequently $f(b)-f(a)\le \log 2+f(b-a-1)\ll_k (1+b-a)^\alpha$. Telescoping on the shorter range now gives
$$
\sum_{t=T}^{T+H-1} D_t
\le 2h\,[f(T+H+h)-f(T-h)]
\ll_k h(H+2h)^\alpha .
$$
It follows that
$$
\frac1H\sum_{2^T\le n<2^{T+H}}\frac{E_k(n)}{n}
\ll_k \frac{\log T}{H^{1-\alpha}}+\frac1T.
$$
For $k=3,4$ the harmonic mean excess therefore tends to zero in **every** such range with $H/(\log T)^2\to\infty$. These ranges can be much shorter on the logarithmic scale than the full interval from $1$ to $2^T$.

## Consequences and the remaining gap

On $G_k$, a uniformly chosen AP-free subset has $(1/2+o(1))r_k(n)$ elements in probability. Indeed (3) and (4) give $2^{o(r)}$ containers of size at most $(1+o(1))r$. For each container, pad it with dummy elements to a common size $\lceil(1+o(1))r\rceil$. Subsets with sizes outside $[(1/2-\varepsilon)r,(1/2+\varepsilon)r]$ number at most $2^{r-\Omega_\varepsilon(r)}$ per container by the binomial tail bound. The denominator is at least $2^r$. This gives an exponentially small exceptional probability for every fixed $\varepsilon>0$.

A sufficient condition for sharp counting at **all** lengths would be $\rho(\lfloor n/(\log n)^{20k}\rfloor)/\rho(n)\to1$. Take this value of $m$ in (2)–(4), with $T\asymp\log n$. The same estimates give $\log_2 I_k(n)\le(1+o(1))r_k(n)$ directly. The average estimate on $D_t$ allows sparse upward jumps and does not establish that condition.

## Appendix. A count at every interval length when the set size is prescribed

Let $I_{k,j}(n)$ count AP-free $j$-element subsets of $[n]$. A refinement of the first-stage argument gives, uniformly for $1\le j\le r=r_k(n)$,
$$
j\log(r/j)\ \le\ \log I_{k,j}(n)\
\le j\log(r/j)+O_k\big(j[\log(e r/j)]^\alpha\big). \tag{6}
$$
In particular, along any sequence with $j/r\to0$, the leading term is $j\log(r/j)$, with no restriction on interval lengths. Here logarithms on both sides are natural. The bound at $j$ comparable to $r$ has additive error of order $r$. It therefore leaves open the all-length leading constant for the total count. The following proof adapts the modular grids and iterative containers in §5 of Morris, Ortega and Rué.

**A modular bound on cheap covers.** For $|B|=\lambda r$, let $v=(\log\lambda)^{1/\alpha}$, $P$ a prime in $(2n,4n)$, $m=\lfloor P e^{-b v}\rfloor$ and $q(\lambda)=e^{-bv/(2k)}$. Choose a fixed $b=b_k>0$ sufficiently small. We claim that for all sufficiently large $n$ and $\lambda\ge\lambda_0(k)$ the set $B$ cannot have a cheap cover at $q(\lambda)$.

To see the parameter ranges uniformly, $\lambda\le n/r\le \exp(C_k(\log(en))^\alpha)$ gives $bv\le (\log n)/2$ for all large $n$ after decreasing $b$. Thus $m$ grows at least on the order of $\sqrt n$, and $P/m\le 2e^{bv}$. After fixing $b$, increase $\lambda_0$ so $m\le n/4$ and $q(\lambda)\le1/(8k^2)$.

In $\mathbb F_P$, choose a uniformly random affine image $J=a[m]+c$ with $a\ne0$. The one-point probability is $m/P$ and the conditional inclusion probability of a second specified point is $(m-1)/(P-1)$ by double transitivity. A cheap cover then gives an expected surviving size at least
$$
|B|\frac mP \left(1-q(\lambda)^{1-k}\frac{m-1}{P-1}\right)
\ge \tfrac12 |B|m/P
$$
for large $\lambda$, by the same deletion argument as in (2). The surviving indices in $[m]$ are AP-free. Indeed an AP of indices would give a modular AP in $[n]$. Each successive second difference of its integer entries has absolute value at most $2(n-1)<P$ and vanishes modulo $P$, so all vanish as integers. The resulting progression is nonconstant since $a\ne0$ and $m<P$. Hence the surviving size is at most $r_k(m)$.

For $s=\lfloor n/(2m)\rfloor$, the digit construction gives $r_k(n)\ge r_k(m)r_k(s)$. Use numbers $x+2my$, with the low digits drawn from an extremal subset of $\{0,\ldots,m-1\}$ and the high digits from one of $\{0,\ldots,s-1\}$, then translate the construction into $[n]$. In any progression the low-digit second differences are multiples of $2m$ of absolute value less than $2m$. Thus the two digits progress separately and both must be constant. Moreover $ms/P\gg1$ and $\log(es)\le O(1)+bv$. By the extremal lower bound,
$$
\frac{|B|m}{P\,r_k(m)}
\ge \lambda\frac{m}{P}r_k(s)
\gg_k \lambda\exp\{-C'_k b^\alpha\log\lambda\}.
$$
Decrease $b$ so $C'_k b^\alpha<1/2$, then take $\lambda_0$ sufficiently large. This ratio exceeds $2$, contradicting the preceding upper bound on the surviving size. This proves the claim.

**Iteration with a variable parameter.** Fix $\Lambda\ge\lambda_0$. If $n\le 2\Lambda r$, take $[n]$ alone. Otherwise start at scale $n/r$ and halve until the first scale in $(\Lambda,2\Lambda]$. To go from cap $2\lambda r$ to $\lambda r$, apply the container theorem to each parent above the target size with $q=q(\lambda)$. A child $B$ with $|B|=\mu r>\lambda r$ has a cheap cover at $q(\lambda)$. The same cover is cheap at $q(\mu)\le q(\lambda)$, because for $s\ge2$ and $q'\le q$ we have $(q')^s\le(q'/q)q^s$. This contradicts the modular bound just proved. Parents below the target cap may be carried forward.

The log number of children of one parent is
$$
O_k\big(r\lambda q(\lambda)\log(e/q(\lambda))\big)
\ll_k r\exp\{-c_k(\log\lambda)^{1/\alpha}\}
$$
for some $c_k>0$. Here $1/\alpha>1$, so the linear term $\log\lambda$ and the logarithmic terms in the exponent can be absorbed by decreasing $c_k$. Summing up the scales $\lambda,2\lambda,4\lambda,\ldots$ gives a geometric bound, since $(x+j\log2)^{1/\alpha}\ge x^{1/\alpha}+j\log 2$ for all sufficiently large $x$. Consequently there are at most
$$
\exp\!\left(C_k r\exp\{-c_k(\log\Lambda)^{1/\alpha}\}\right)
$$
containers of size at most $2\Lambda r$. This also implies (1).

Finally choose $\Lambda=\exp(A_k[\log(e r/j)]^\alpha)$ with $A_k$ large enough that $\Lambda\ge\lambda_0$ and the log family size is $O_k(j)$. Each container contributes at most $(2e\Lambda r/j)^j$ sets of size $j$. The lower bound follows from $\binom{r}{j}\ge(r/j)^j$ subsets of an extremal set. This proves (6).

## Checks

The hand checks covered restriction of a hypergraph to successive containers, the distinction between the parent and child in Theorem A, the grid endpoints, integer rounding, covers at a smaller parameter, and the harmonic mass up to a partially completed block.

For the integer-grid calculation, enumeration used $2\le n\le31$, $1\le m\le\min(n,8)$, and $2\le d\le9$. Across 1,752 parameter triples it checked 31,064 single-point incidence counts and 316,432 pair counts. For $x<y$ the exact number of pairs $(p,b)$ whose grid contains both is
$$
\sum_{\substack{p\le d\text{ prime}\\p\mid y-x}}
\max(0,m-(y-x)/p).
$$
For the modular grid, enumeration checked 6,906 pair counts over $P\in\{5,7,11,13,17,19\}$ and $1\le m<P$. Exhaustive subset enumeration also verified the digit-product inequality in all 216 cases with $2\le n\le17$, $k\in\{3,4,5\}$, and $1\le m\le\lfloor n/2\rfloor$. These checks test the finite identities used in the argument. The asymptotic conclusions follow from the proof above.