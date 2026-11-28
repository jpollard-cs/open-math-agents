# Cap and reciprocal estimates near a linear number of distinct supports per digit

Codex (OpenAI). AI-authored written companion to the [component cap estimate](component-cap.md) and [articulation bound](articulation-surplus.md) for Erdős #1189.

## Largest modulus

Let $D$ be **any** irreducible set of $k$ distinct moduli with largest modulus $X$. Reserve one row and order a partition of the CRT digit positions, as in the cap estimate. The internal support of each remaining row consists of its tests in the last block it meets. For each support, project the holes left by earlier rows onto all earlier positions tested in its group, minimizing the number of different projected patterns over earlier assignments. Suppose this minimum is at most a fixed $A\ge1$ for singleton supports and at most $B\le X^{b+o(1)}$ for mixed supports, with fixed $0\le b<1$. Different groups may minimize separately.

Assign **each distinct mixed support once** to its position of smallest base prime $p$, breaking ties by the smallest position index $j$. Assume the number charged to any $(p,j)$ is bounded by a common finite function $H(p)$ with
$$
                  \limsup_{p\to\infty} H(p)\log p/p\le\lambda<\infty .
$$
Then
$$
 k\le\left(1+\log A+
         \left(\frac4{1-b}-2\right)\log(1+\lambda)+o(1)\right)
         \frac{X}{\log X}.
$$
In particular $A=1$ and $H(p)=o(p/\log p)$ give the sharp leading constant one, even with polynomially many earlier patterns on the mixed supports. Ordinary digit covers realize that constant at all sufficiently large exact sizes. At $H(p)=O(p/\log p)$ and fixed $A,b$ the order $X/\log X$ persists. The explicit constant for positive $\lambda$ is an upper bound.

**Proof.** Each group with support $I$ has at most $\min(BP(I), X/m(I))$ rows if it is mixed. Here $P(I)$ is the product of the alphabets of its positions with multiplicity, and $m(I)$ is the lcm of their prime powers. This follows by [reassigning the rows to all visible patterns](component-cap.md), together with integer distinctness. Since $P(I)\le m(I)$ each mixed group has at most $\sqrt{BX}$ rows. Every present prime has $p^{e+1}\le X$ at its highest digit $e$, since a fibre of size $p$ must be covered by distinct multiples of $p^e$. The earlier singleton calculation contributes at most $(1+\log A+o(1))X/\log X$, including all higher digits and the reserved row.

Put $z=(X/B)^{1/4}$. It grows at least as a fixed positive power of $X$. The positions with $p\le\sqrt z$ carry $O(\sqrt{BX}\, z\log X)=o(X/\log X)$ rows since $H(p)=O(p)$ and there are $O(\log X)$ positions per prime. For $\sqrt z<p\le z$ the number of positions per prime is bounded in terms of $b$, and $\sum_{p\le z} H(p)=O(z^2/(\log z)^2)$ by Chebyshev's bound. Multiplying by $\sqrt{BX}$ gives $O_b(X/(\log X)^2)$ with constants also depending on the envelope.

For $p>z$, any shape with at least three positions has $m(I)\ge P(I)\ge p^3$. For two different bases the same estimate holds if either tested position is higher than the first. These shapes contribute $O_b(X\sum_{p>z} H(p)/p^3)=o(X/\log X)$ since only boundedly many positions per prime occur. For two positions of the same base there are $O_b(1)$ possible pairs per base, each occurring as an internal support in at most one block. These contribute $O_b(X\sum_{p>z}1/p^2)=o(X/\log X)$.

Only first-digit pairs of different primes $p<q$ remain. A pair occurs in at most one block. At each $p$ its larger neighbors are distinct, at most $H(p)$ in number. For any fixed $t>\lambda$ the prime number theorem gives at least $H(p)$ primes in $(p,(1+t)p]$ for sufficiently large $p$. Replacing the neighbors by the first $H(p)$ primes above $p$ can only increase the reciprocal sum. Uniformly as $p>z\to\infty$, partial summation on the fixed ratio interval gives a sum at most $(\log(1+t)+o(1))/\log p$. The pair groups contain at most $X/(pq)$ rows apiece. Finally
$$
 \sum_{z<p\le\sqrt X}\frac1{p\log p}
  =\frac1{\log z}-\frac2{\log X}+o(1/\log X)
  \le\frac{4/(1-b)-2+o(1)}{\log X}.
$$
The equality follows by partial summation from the prime number theorem, including when $B$ varies. Let $t\downarrow\lambda$. This proves the estimate with its original uniform quantifiers.

## Reciprocal sum

For a full-period set take a successful assignment and split its strongly connected digit components into vertex-biconnected blocks as in the [articulation bound](articulation-surplus.md). Now count all distinct mixed supports incident to a digit in each block separately. If these counts are at most $H(p)$ for each digit of base $p$, the following upper bounds on $S-\Phi(L)$ hold uniformly:
    
* $O(1)$ for $H(p)=O(p/(\log p)^{1+\eta})$ with any fixed $\eta>0$.
* $O(1+\log\log k)$ for $H(p)=O(p/\log p)$.
* $O((1+\log\log k)^2)$ for $H(p)=O(p(1+\log p)^A)$ for any fixed $A\ge0$.

For general $p^{1+o(1)}$ incidence the [separated-prime theorem](separated-prime-layers.md) gives $o(\log k)$ as an upper bound. All are class results; finiteness of the unrestricted additive surplus remains open.

**Proof.** Discard rows above $k$ at cost at most one. Singletons cost at most $\Phi(L)$ and the terminal costs at most one. Root each block-cut tree and call a position new in its unique introduction block. Mixed supports with just one new position are parent–new pairs. Their combined cost is bounded by the parent–child Hölder estimate in the [articulation proof](articulation-surplus.md), since $H(p)$ is bounded by a fixed power and at most $p-1$ blocks meet at a digit of base $p$. This estimate also covers pairs of positions at the same prime.

A support group costs at most $f(m)=(1+\log m)/m$, decreasing for $m\ge1$. For a support with at least three new positions, charge any new position of smallest base $p$. If its index is $j$ then $m\ge\max(p^3,p^j)$, since $m\ge P(I)$. There are at most $H(p)$ charges there. Thus the total is bounded by a constant multiple of $\sum_p H(p)(1+\log p)/p^3$, finite in all the stated cases. A given pair of exactly two new positions gives at most two supports, with or without the one parent. For same-base pairs sum $2\sum_p\sum_{j\ge2}(j-1) f(p^j)<\infty$.

For two new positions of different bases write their numerical prime powers as $a=p^j<b=q^l$. Each group costs at most $f(ab)\le f(a^2)$. Thus the cost charged to $a$ is at most $H(p)f(a^2)$. Summing over $j\ge2$ costs $O(1)$. For $j=1$ this gives the first two conclusions by the prime reciprocal theorem and partial summation.

For the third conclusion fix a smaller numerical prime power $a$ and split its partners at $Y=a(1+\log a)^{A+3}$. Above $Y$ there are at most $H(p)$ groups and each costs at most $f(aY)$, giving $O_A(1/(a(1+\log a)^2))$. Below $Y$ every partner occurs at most twice. The number of prime powers up to $x$ is $O(x/\log x)$ by Chebyshev's estimate and the elementary count of higher powers. Summing over dyadic intervals from $a$ to $Y$ gives $\sum_{a\le b\le Y} 1/b\ll_A (1+\log\log(3a))/\log(2a)$ over numerical prime powers $b$. Since $\log(aY)=O_A(\log(2a))$, the cost is $O_A((1+\log\log(3a))/a)$. Only $a\le k$ occur after truncation. The sum over prime powers with exponent at least two is bounded; the sum over primes is $O_A((1+\log\log k)^2)$ by partial summation. No uniform bound on the number of vertices of a block is required.

[Original problem](https://www.erdosproblems.com/1189) · [Every-size constructions](../reciprocal-sums/) · [Independent arithmetic checks](support-endpoint-check.py). The asymptotic estimates are written proofs. The unresolved issue for the minimum is whether a general cover can simultaneously exceed these support budgets and keep its densely overlapping rows indispensable.
