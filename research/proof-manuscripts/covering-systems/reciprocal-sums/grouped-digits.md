# What grouping prime-power digits can achieve in Erdős #1189

Codex, at the request of Jordan Pollard · 27 November 2026 · mathematical note for review

Let $A$ be an irreducible set of $k$ distinct covering moduli greater than one. Write $M=\max A$, $L=\operatorname{lcm}(A)$ and $S(A)=\sum_{n\in A}1/n$. Irreducible means no proper subset can cover, even after freely choosing new residues. This note proves two extremal statements for a specified class and necessary conditions for an unrestricted improvement. Logarithms are natural.

## Which covers are included?

Write the digits of $L$ as $(p,j)$ for primes $p\mid L$ and $1\le j\le v_p(L)$. For a nonempty block $B$ of digits set

$$
r_B=\prod_{(p,j)\in B}p,\qquad D_B=\operatorname{lcm}_{(p,j)\in B}p^j.
$$

Partition the digits into disjoint blocks. In each block place at most $r_B-1$ members of $A\setminus\{M\}$, each a multiple of $D_B$. Each modulus can be placed only once. Let $h(A)$ be the minimum number left unplaced over all partitions and placements. Blocks may be empty of moduli. This is a divisibility and cardinality condition, independent of the covering residues.

The singleton partition and the matching lemma in the [companion manuscript](./erdos1189-reciprocal-sums-and-exact-minima.pdf) give $h(A)\le\delta(A)$, where $\delta(A)=k-1-\sum_{p\mid L}v_p(L)(p-1)$. Grouping can make this inequality strict by a linear amount, as the example below shows.

## Two sharp conclusions when all remaining moduli can be placed

Among the covers with $h(A)=0$ the least possible $M$ is $(1+o(1))k\log k$. The greatest possible $S(A)$ equals the zero-defect maximum $R_0(k)$ up to additive $o(1)$, including its constant term. The construction from the companion manuscript attains both estimates at each sufficiently large exact size. The same leading estimate for the least maximum holds over any larger class with a uniform $h=o(k)$ bound that contains the zero-defect constructions.

**Reciprocal sums.** Write $H_t=\sum_{s=1}^t1/s$. A block contributes at most $H_{r_B-1}/D_B$. For integers $a,b\ge2$,

$$
H_{ab-1}-H_{a-1}=
\sum_{t=1}^{b-1}\sum_{s=0}^{a-1}\frac1{at+s}\le H_{b-1}.
$$

Iteration and $p^j\mid D_B$ give the exact inequality

$$
\frac{H_{r_B-1}}{D_B}
\le \sum_{(p,j)\in B}\frac{H_{p-1}}{p^j}.
$$

Consequently when $h=0$, $S(A)\le 1/M+U(L)$, with $U(L)=\sum_{(p,j)} H_{p-1}/p^j$. Sections 1 and 3 of the companion manuscript bound $U(L)$ by the same prime sum $W(z)$ for every irreducible cover of size $k$, and construct a zero-defect cover attaining $W(z)-o(1)$ at every sufficiently large $k$. Since $1/M\le1/(k+1)$ this proves the stated comparison with $R_0(k)$. In particular the common expansion is $\tfrac12\log k+(\tfrac12+\gamma)\log\log k+C+o(1)$ with the same $C$ as in that manuscript.

**Counting moduli.** For every irreducible $A$,

$$
k-1-h(A)\le(1+o(1))\frac{M}{\log M},\qquad M\longrightarrow\infty. \tag{1}
$$

For each $p^a\parallel L$ the prime-power fibre bound in section 4 of the companion manuscript gives $(p+1)p^a\le M$. Thus each active prime is at most $\sqrt M$. The singleton blocks $(p,1)$ can hold at most $\sum_{p\le\sqrt M}(p-1)\sim M/\log M$ moduli by the prime number theorem and partial summation. Singleton blocks $(p,j)$ with $j\ge2$ have $p\le M^{1/3}$. They hold $O(M^{2/3}\log M)$ moduli altogether, by bounding the number of positions per prime by $\log_2 M$ and the sum of these primes by the sum of all integers up to $M^{1/3}$.

For a block containing at least two digits, let $p$ be its smallest prime and $j$ its largest position at that prime. Disjoint blocks have different charges $(p,j)$. Also $D_B\ge r_B\ge p^2$, since at each prime the largest position is at least the number of selected positions. The number placed in the block is at most $\min(r_B-1,M/D_B)\le\min(\sqrt M,M/p^2)$. There are at most $\log_2 M$ possible charges at each $p$. Below $M^{1/4}$ bound each by $\sqrt M$. Above it use $M\sum_{n>M^{1/4}}n^{-2}=O(M^{3/4})$. The total across these blocks is $O(M^{3/4}\log M)=o(M/\log M)$. This proves (1). In particular, if $M\le(1-\varepsilon)k\log k$ for fixed $\varepsilon>0$, then $h(A)\ge(\varepsilon-o(1))k$, since $M\ge k+1$. The companion construction gives the matching upper estimate within $h=0$.

## A reciprocal bound even when some placements fail

Every irreducible $A$ satisfies

$$
S(A)\le\tfrac12\log k+(1-\log 2)\log(1+h(A))+O(\log\log(k+3)). \tag{2}
$$

For any disjoint partition the total *uncut* reciprocal mass in blocks of two or more digits is bounded by an absolute constant. Charge them as in (1). Since $D_B\ge\max(p^2,p^j)$ and $(1+\log x)/x$ is decreasing for $x\ge1$, each contributes at most $(1+t\log p)/p^t$, where $t=\max(2,j)$. Summing over $j\ge1$ costs $O((1+\log p)/p^2)$ per prime. The sum of these bounds converges even over all integers $p\ge2$.

For precision, put $I(L)=\{p^j d:(p,j)\text{ a digit of }L,\ 1\le d<p\}$. For every $y\ge1$, put $w(n)=\min(1/n,1/y)$ and $g(n)=(1/n-1/y)_+$. A singleton row contributes at most the sum of $w$ on its $p-1$ smallest possible multiples. These ideal entries are distinct even between different rows, since $p$ is their largest prime and $j$ its exponent. Adding the ideal entries for unused singleton positions only increases the bound. The grouped rows cost $O(1)$ in $w$, and the unplaced moduli cost at most $h/y$. Summing $g$ over all divisors of $L$ at least two, and cancelling the ideal terms in $\sum_{n\in I(L)}w(n)=U(L)-\sum_{n\in I(L)}g(n)$, gives

$$
S(A)\le 1/M+U(L)+O(1)+h/y+
\sum_{\substack{2\le n\le y,\; n\mid L\\n\notin I(L)}}(1/n-1/y).
$$

As proved in the [defect estimate](./defect-tradeoff.md), the last sum is at most $(1-\log 2)\log y+O(1+\log\log(y+3))$. Take $y=h+1$ and use the prime-budget upper bound on $U(L)$ to obtain (2). A fixed gain $S(A)\ge(1/2+\varepsilon)\log k$ requires $h(A)\ge k^{\varepsilon/(1-\log2)-o(1)}$.

## Examples and the unresolved step

Öztürk's Lemma 6.2 gives irreducible sets $C_n=\{2^i:1\le i<n\}\cup\{2^i n:0\le i<n\}$ for odd $n\ge3$. For $n=3^a$, use singleton blocks for the binary powers and a single block containing all $a$ ternary positions. The latter holds the $n-1$ odd-factor moduli left after reserving $M=2^{n-1}n$. Thus $h=0$, while $\delta=n-1-2a$ and $k=2n-1$. In particular $\delta/k\to1/2$. The construction itself is due to Öztürk. [Preprint, Lemma 6.2](https://www.researchgate.net/publication/413884122)

There is also a finite obstruction. The irreducible set $\{3,4,5,6,8,9,10,12,15,18,20,24,36,40\}$ has $L=360$. Among all 203 partitions of its six prime-power digits, the best places 12 of the 13 moduli remaining after reserving 40. Thus $h=1$. The unique size-25 example at cap 60 has $h=3$ (all 4,140 partitions tested). To reproduce the first calculation run:

```sh
python block_test.py 3 4 5 6 8 9 10 12 15 18 20 24 36 40
```

For each partition the program expands the available capacities into a bipartite graph and uses augmenting paths to find a maximum matching. The period for the digit set always includes the reserved largest modulus. Irreducibility of these examples can be checked in the accompanying finite catalogs. Controlling the number or the reciprocal weight of unplaced moduli in general remains open here.
