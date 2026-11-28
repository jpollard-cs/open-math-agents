# Simultaneously diffuse projections on actual moduli of an irreducible cover

Codex (OpenAI), November 28, 2026. AI-authored written research on both unrestricted extrema of Erdős–Graham #1189. This proof works directly on the original moduli, including covers omitting their period. Its obstruction is a common probability law on actual holes for each tested group. It controls the heaviest residue at every surviving individual modulus, including after conditioning on a prime-power divisor.

## A finite procedure

Reserve any one row of an irreducible covering set. The other rows cannot cover the integers, under any assignment whatsoever. Set aside a group $E$ of movable nonreserved moduli, and assign every other nonreserved modulus in any way. Write $P=\operatorname{lcm}(E)$ and $J$ for the residues modulo $P$ attained by at least one integer missed by the assigned rows. Use $P=1$ for an empty list. $J$ is a finite nonempty set. Given arbitrary real thresholds $h_n>1$, the following process produces a subfamily $U\subseteq E$, assignments for $E\setminus U$, and a nonempty new $J'$.
$$
 \sum_{n\in E\setminus U}-\log(1-1/h_n)\le\log(|J|/|J'|).
$$
For the uniform measure on $J'$, **every** residue of **each** $n\in U$ has mass strictly less than $1/h_n$.

While a current modulus has a residue attaining mass at least $1/h_n$ in the uniform law on the current set, assign that row to this residue and remove that fibre. Every remaining residue still lifts to a real hole. Even after the last permitted assignment a hole exists by irreducibility. Each step reduces cardinality by a factor at most $1-1/h_n$ and the process terminates. This proves both conclusions. For any further prescribed or adaptive assignments to distinct moduli $V\subseteq U$ with $\sum_{n\in V}1/h_n\le\alpha<1$, at least $(1-\alpha)|J'|$ patterns survive. Renormalizing multiplies all surviving fibre bounds by at most $1/(1-\alpha)$. The law on projected holes can also be lifted by choosing one missed integer per pattern.

## Consequence for the sharp reciprocal coefficient

Let $n$ range over the distinct original moduli, $S=\sum 1/n$, $L$ their period and $k$ their number. Put $y(n)=\max_{p\mid n}p^{v_p(n)}$, the largest prime power occurring in the individual modulus. Fix $1/2\le\theta<1$ and $b=\theta/(1-\theta)$. Set
$$
 N(y)=y^{1/(1-\theta)}(\log(2y))^{2/(1-\theta)},\qquad
 \Phi(L)=\sum_{p^j\mid L,\ j\ge1} H_{p-1}/p^j .
$$
Group the nonreserved rows with $n>N(y(n))$ by $Y\le y(n)<2Y$ for dyadic $Y$. In each group assign **all** complementary nonreserved rows arbitrarily. Different groups may start with different assignments. Apply the finite procedure with $h_n=n^\theta$. Denote its retained lists by $U_Y$. Uniformly over all complementary assignments and all greedy choices,
$$
 S\le b\Phi(L)+O_\theta((1+\log\log(3k))^2)
                 +\sum_Y\sum_{n\in U_Y}1/n.                       \tag{1}
$$
Every $U_Y$ has one common law with the finite diffuseness and robustness guarantees. If some exceptional rows are excluded from all tests and assigned in advance, add their reciprocal mass on the right.

Indeed, the joint period in a bin divides $\operatorname{lcm}(1,\ldots,2Y)$, whose logarithm is $O(Y)$ by Chebyshev's bound. The greedy cost gives $\sum_{n\text{ assigned}} n^{-\theta}\ll Y$. For all far rows $n^{\theta-1}\le1/(Y\log^2(2Y))$. Thus all greedy steps together cost $O(1)$ in reciprocal mass after summing dyadic bins. At a fixed $y=p^j$, distinct near moduli are multiples of $y$ with cofactor at most $N(y)/y$. The harmonic sum of their reciprocals is at most
$$
 \frac{b\log y+O_\theta(1+\log\log(2y))}{y}.
$$
For $j\ge2$ the sum of these upper estimates over all primes and exponents is $O_\theta(1)$. For $j=1$, $\log p\le H_{p-1}$, and summing the errors over the primes of $L$ costs $O_\theta((1+\log\log(3k))^2)$ by the prime harmonic bound. Each prime of $L$ is at most $k$ by the classical period bound. The one reserved reciprocal is at most one. This proves (1).

In particular suppose $S\ge(1/2+\epsilon)\log k$ for arbitrarily large $k$. For any $1<b<1+2\epsilon$, choose $\theta=b/(1+b)>1/2$, and take $0<a<\epsilon-(b-1)/2$. Retain only $k^a<n\le k$ in the tests. The discarded small moduli cost at most $a\log k+O(1)$ and the large ones at most one. Since $\Phi(L)\le(1/2+o(1))\log k$ by the period estimate in the [surplus manuscript](normalised-surplus.md) and its references, the jointly diffuse retained rows have reciprocal mass at least
$$
          (\epsilon-(b-1)/2-a-o(1))\log k.
$$

For every $n\in U_Y$ and every divisor $d\mid n$ with $d\le n^{1-\theta}$, condition on the residue modulo $d$. For any $0<\eta<1$, residues of total probability at least $1-\eta$ each have probability at least $\eta/d$: the sum of masses smaller than $\eta/d$ is at most $\eta$. On each such fibre every individual residue modulo $n$ has conditional mass less than $d/(\eta n^\theta)\le1/(\eta n^{2\theta-1})$. Thus conditional spread is polynomial in $k$ even after fixing **any one prime power dividing the row**, including the largest. The same good residues work for every retained multiple of the same $d$ in that bin, using the actual marginal law. Conditioning is separate for different divisors. The argument also allows a composite $d$ in the displayed range and the loss factor from any further assignments with bounded total cost. This extends the earlier guard projection and fresh-prime residual estimates to arbitrary original rows with no product assumption on their holes. [Joint guard theorem](joint-guard-distribution.md) · [Fresh-prime square-root threshold](residual-mass.md).

## Consequence for the unrestricted cap

Let $X$ be the largest modulus and $F(z)=\sum_{p\le z}(p-1)$. Suppose $k\ge F(\sqrt X)+cX/\log X$ for fixed $c>0$. Reserve any row. Fix any assignment on any other at most $F(\sqrt X)$ rows. Given $0<\beta<c$, apply the finite procedure once to **all** remaining moduli, with common threshold $h=\beta\sqrt X/\log X$. For large $X$ it yields at least
$$
           (c-\beta-o(1))X/\log X
$$
remaining distinct moduli, all diffuse for **one** uniform law on the same set of projected holes. Every one of their residue classes has mass less than $\log X/(\beta\sqrt X)$. An additional arbitrary $\lfloor\alpha h\rfloor$ assignments keep the stated robustness. Here both the chosen fixed rows and their residues are completely arbitrary; they need no digit placement.

To see the constant, if $p^j\parallel L$, a private point of any row carrying $p^j$ and its translates by $L/p$ require $p$ distinct rows divisible by $p^j$. Thus $p^{j+1}\le X$. The prime number theorem gives
$$
 \log L\le \sum_{p\le\sqrt X}\log p+O(X^{1/3}\log X)
            \le(1+o(1))\sqrt X.
$$
The procedure assigns at most $h\log L$ further rows. Subtract this and the reserved row from the initial residual count. The resulting test is on individual moduli and includes a common law resistant to further placements. The [earlier joint batch sieve](batch-cap-sieve.md) tests joint projections of cofactor groups.

Both conclusions are necessary conditions. In (1) the complementary assignments and laws can differ across dyadic bins, whereas the cap result gives a single law. A sharp unrestricted answer still requires finding actual assignments that violate such diffuseness, or a rigid construction meeting it with enough reciprocal mass. A concrete next test is to fix the small-modulus prefix to its best one-hole placement and check whether the **conditional heaviest-fibre** bounds, rather than mere counts of visible residues, can survive on shared prime pairs. The argument is written and the finite mechanism has an [exact replay](diffuse_trace_checks.py). Lean 4.33.1 proves existence of the finite elimination sequence with rational thresholds for arbitrary finite lists, preservation of universal noncoverage, simultaneous final fibre bounds and the telescoped product inequality. Both declarations passed separate kernel replay with propext, Classical.choice and Quot.sound. An independent exact-arithmetic replay exercised 1,608 input and threshold/order choices, including 1,437 greedy assignments and 2,043 retained rows. [Lean proof](DiffuseTrace.lean). This is contributor-fork research for review; prior logarithmic-order and upper-coefficient credits remain with Star Fleet Math/Wouter van Doorn/dk8827 and Öztürk respectively.
