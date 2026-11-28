# A sharp asymptotic for one class of irreducible covers

Codex, at the request of Jordan Pollard · 27 November 2026 · research note for review

Fix an irreducible covering set $A$ of $k$ distinct moduli greater than one. Irreducibility allows arbitrary reassignment of residues when a modulus is removed. Write $M=\max A$, $L=\operatorname{lcm}(A)$, and use natural logarithms. The unrestricted minimum in Erdős #1189(ii) is $m(k)$. We prove an asymptotic expansion for a restricted minimum, an obstruction for the unrestricted problem, and a sharp law for the sizes of the individual moduli.

## The restriction and the results

For each prime power $p^a\parallel L$ there are digits $(p,1),\ldots,(p,a)$. Partition all digits into blocks. A block $B$ has capacity $r_B-1$, where $r_B=\prod_{(p,j)\in B}p$. An entry may occupy the block if it is divisible by $D_B=\operatorname{lcm}_{(p,j)\in B}p^j$. Reserve $M$, and assign each of the other entries at most once. Write $h(A)$ for the smallest number of these entries that must remain unassigned. Let $m_g(k)$ be the minimum $M$ over covers with $h(A)=0$, and $m_0(k)$ the minimum over covers with $k=1+\sum_{p^a\parallel L}a(p-1)$ (zero defect). The matching lemma gives $h=0$ in the latter class. The grouped class also includes examples with defect proportional to $k$, and covers with $h>0$ exist. [Grouped examples and definitions](./grouped-digits.md)

Put $F(z)=\sum_{p\le z}(p-1)$ and $J(x)=\int_2^x dt/\log t$ for $x\ge2$.

1. For some absolute $c>0$, **both** $m_g(k)$ and $m_0(k)$ equal $J^{-1}(k)+O(k\exp(-c\sqrt{\log k}))$. In particular both equal
$$
k\left(\log k+\log\log k-1+
\frac{\log\log k-2}{\log k}
+O\left(\frac{(\log\log k)^2}{(\log k)^2}\right)\right).
$$
2. **Every** irreducible cover with $M\le k\log k$ satisfies $h(A)\ge (k/\log k)(\log\log k-1-o(1))$. Thus the restricted result supplies a necessary condition for a smaller unrestricted minimum.
3. Suppose $k\to\infty$, $h(A)=o(k)$ and $M\sim k\log k$. For any fixed $0<s<1$,
$$
\liminf\frac{\#\{n\in A:n>sM\}}{k}\ \ge\ 1-s+s\log s .
$$
The exact-size zero-defect construction attains equality in the limit for every $s$ along the same sequence. For example, at least $15.34\%$ of the moduli exceed half the largest in the limit. For every fixed $r>0$, the sharp lower bound on the limiting inferior of the mean of $(n/M)^r$ is $1/(r+1)^2$.

## Counting with a cap on the largest modulus

Let $K_{\rm all}(X)$ be the largest $K$ such that every integer $5\le k\le K$ occurs with zero defect under cap $X$. Let $K_{\rm max}(X)$ be the largest cardinality of a cover with $h=0$ under that cap. We prove
$$
F(\sqrt X)-O(X^{3/4}\log X)
\ \le K_{\rm all}(X)\le K_{\rm max}(X)
\ \le F(\sqrt X)+O(X^{3/4}\log X). \tag{1}
$$

In any irreducible cover the prime-power fibre bound gives $(p+1)p^a\le M$ for $p^a\parallel L$. Indeed, choose a point missed by the rows whose moduli omit the highest $p$-digit. Changing that digit leaves those rows missing. The $p$ digit values require at least $p$ distinct multiples of $p^a$. If $M<(p+1)p^a$, the available multipliers belong to $1,\ldots,p$, with $p$ impossible by maximality of $a$. That leaves fewer than $p$ rows. [Fibre bound and every-size construction, sections 2–4](./erdos1189-reciprocal-sums-and-exact-minima.pdf)

For an optimal placement, let $c_p$ count entries in the singleton block $(p,1)$, taking zero if it is absent. Each $p\le z=\sqrt M$ and $c_p\le p-1$. Higher singleton digits can account for $O(M^{2/3}\log M)$ entries, since $p\le M^{1/3}$ there and each prime has at most $\log_2 M$ positions. Charge a block of at least two digits to its smallest prime $p$ and the highest position of $p$ in that block. Charges are distinct, and $D_B\ge r_B\ge p^2$. Such a block can hold at most $\min(\sqrt M,M/p^2)$ entries, by its capacity and the count of multiples of $D_B$. Splitting the sum at $M^{1/4}$ and bounding primes by all integers gives $O(M^{3/4}\log M)$ entries from these blocks. Therefore
$$
k-1-h(A)=\sum_{p\le z}c_p+O(M^{3/4}\log M)
\ \le F(z)+O(M^{3/4}\log M). \tag{2}
$$
This gives the upper side of (1).

For the lower side, use the exact-size construction in the linked manuscript. Let $u$ be the first integer with $B_*(u)=1+\sum_{p^j\le u}(p-1)\ge k$. Its zero-defect constructor removes the top power at each of $O(\log u)$ selected primes. Each removed power exceeds $\sqrt u$. For $p\le\sqrt u$ the nonterminal entries are at most $u^{3/2}$. For larger $p$ each exponent is one. In each such row the estimate in section 2 gives enough divisors with cofactor at most $p+O(p\log u/\sqrt u+1)$, with compulsory terminal cofactors at most $u$. Thus its largest modulus is at most $u^2+C u^{3/2}\log u$. Also $B_*(u)=F(u)+O(u\log u)$ and its last jump is at most $u$. Bounded small sizes have zero-defect covers by the elementary binary construction in the same source.

Choose $v=\lfloor\sqrt X-C'X^{1/4}\log X\rfloor$ for a sufficiently large constant $C'$. Every $k\le B_*(v)$ with $k\ge5$ now fits under $X$, since $u\le v$. The missing interval costs $F(\sqrt X)-F(v)\le (\sqrt X-v+1)\sqrt X$. This proves (1) without a prime number theorem or any monotonicity assumption on the minimum at successive sizes.

## Inversion and the unrestricted obstruction

The classical prime number theorem with its de la Vallée Poussin remainder, followed by partial summation, gives
$$
F(\sqrt X)=J(X)+O\big(X\exp(-c_1\sqrt{\log X})\big).
$$
The main integral follows from $\int t\,dt/\log t=J(t^2)+\text{constant}$. The subtraction of $\pi(\sqrt X)$ lies within the error. Formula (1) now bounds both cap functions by the same error about $J(X)$. At $x=J^{-1}(k)\asymp k\log k$, changing the cap by $\pm k\exp(-c\sqrt{\log k})$ changes $J$ by more than this error for sufficiently small $c>0$, since $J'(x)=1/\log x$. The lower cap cannot contain any size-$k$ cover with $h=0$, and the upper cap contains a zero-defect example. This proves assertion 1, including all fixed orders of the inverse-logarithmic-integral expansion. [Classical prime-sum estimate, Axler](https://cs.uwaterloo.ca/journals/JIS/VOL22/Axler2/axler24.pdf)

For fixed real $a,b$, insertion of $X=k(\log k+a\log\log k+b)$ in (2) gives, whenever $M\le X$,
$$
h(A)\ge\frac{k}{\log k}\left((1-a)\log\log k-1-b
-O\left(\frac{(\log\log k)^2}{\log k}\right)\right).
$$
Indeed $J(X)=X/\log X+X/\log^2 X+O(X/\log^3 X)$; expanding the first two denominators gives the displayed bound. Taking $a=b=0$ proves assertion 2. A cap of $k(\log k+\log\log k-1-c)$ with fixed $c>0$ requires at least $(c-o(1))k/\log k$ unassigned entries. The estimate does not limit how large $h(A)$ can be in general.

## A sharp distribution for the moduli

Under the hypotheses of assertion 3, $F(z)\sim k$. By (2) the total shortage $D=\sum_{p\le z}(p-1-c_p)$ is nonnegative and $o(k)$. In particular for any fixed $0<t\le1$, the fraction of all entries assigned to first-digit singleton rows with $p\le tz$ tends to $t^2$. This holds for every optimal placement, since their common shortage bound is uniform.

At most $\lfloor sM/p\rfloor$ distinct multiples of $p$ are at most $sM$. Each first-digit row must place its remaining multiples above that threshold. Since $x\mapsto(x-u)_+$ is 1-Lipschitz, summation gives the finite inequality
$$
\#\{n\in A:n>sM\}\ \ge\ \sum_{p\le z}(p-1-\lfloor sM/p\rfloor)_+-D. \tag{3}
$$
In evaluating the sum we can replace the summands by $(p-sM/p)_+$ with total error $O(\pi(z))=o(k)$. The support is $\sqrt{s}\,z<p\le z$. On this interval the weighted prime sum divided by $k$ tends to $1-s$. Partial summation of the prime number theorem on the same fixed-ratio interval gives $\sum 1/p=(\log(1/\sqrt{s})+o(1))/\log z$. As $k\sim M/(2\log z)$, the subtracted term $sM\sum 1/p$, divided by $k$, tends to $-s\log s$. This proves the lower bound.

For attainment compare the exact-size construction with the set $T_u=\{pd:p\le u\text{ prime},\ 1\le d<p\}$. These entries are distinct since $p$ is the largest prime of $pd$. The terminal row costs $O(u)$ exceptions; the higher powers cost $O(u\log u)$, and the removed rows cost $O(u\log u)$. At a surviving nonterminal first-digit row, every $d<p$ dividing the preceding part of $L$ is among the first $p-1$ eligible divisors, so is used. Only multiples of a removed top power can be missing among $d<p$. There are at most $O(p\log u/\sqrt u)$ of them per row. As $F(u)\sim k$, the total symmetric difference between the constructed set and $T_u$ is $o(k)$. The construction has $M/u^2\to1$ by (1) and its upper bound above. In $T_u$ the number exceeding $su^2$ is exactly $\sum_{p\le u}(p-1-\lfloor su^2/p\rfloor)_+$. The same evaluation gives $k(1-s+s\log s)+o(k)$. Squeezing between the thresholds $(s\pm\varepsilon)u^2$ proves attainment for $sM$ too.

For the moments integrate the tail against $rs^{r-1}\,ds$ on $[0,1]$. Fatou's lemma yields the lower bound; dominated convergence for the constructed sets gives equality. The integral is $1/(r+1)^2$. In particular the limiting mean of $n/M$ is at least $1/4$ and the bound is attained.

[Reproducible finite checks](./check-critical-cap.py) exercise (3) and the comparison with $T_u$ on exact-size examples. The unrestricted minimum for arbitrary $k$ remains unresolved.
