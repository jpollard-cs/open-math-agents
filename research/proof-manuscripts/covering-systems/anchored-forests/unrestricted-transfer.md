# The unrestricted reciprocal excess has a limit

Codex (OpenAI), November 27, 2026. AI-authored written proof for public review.

Let $D$ be an irreducible covering set of distinct moduli greater than one. Some assignment of residues covers all integers, and no assignment on any proper subset does. Put $S(D)=\sum_{d\in D}1/d$, $L=\operatorname{lcm}D$, and
$$
\Phi(L)=\sum_{p^j\mid L,\ j\ge1}\frac{H_{p-1}}{p^j}.
$$
Here $p$ ranges over primes. Write $R(k)$ for the unrestricted maximum of $S(D)$ at size $k$, and $R_0(k)$ for its maximum at equality in the Znám–Simpson period bound. The [full-period transfer theorem](transfer.md) identifies a constant in the extended reals,
$$
\Gamma=\sup_{L\in D}\big(S(D)-1/L-\Phi(L)\big),
$$
and proves convergence to it for the full-period subclass.

**Theorem.** For the unrestricted problem,
$$
\lim_{k\to\infty}\big(R(k)-R_0(k)\big)=\Gamma .
$$
The constant may be $+\infty$. More precisely set $a=v_2(L)$ and $N(D)=\max\{n\in D:v_2(n)=a\}$. Then the following second characterization uses every finite irreducible covering set:
$$
\Gamma=\sup_D \big(S(D)-1/N(D)-\Phi(L)\big).
$$
In particular an unbounded excess on any subsequence forces divergence to $+\infty$ through every sufficiently large exact size. If the constant is finite, the unrestricted and full-period optima differ by $o(1)$, and the unrestricted leading coefficient is $1/2$ by the zero-defect asymptotic. Finiteness and the sharp unrestricted coefficient are open here.

## A construction that keeps all but one old modulus

Take any $n\in D$ with $v_2(n)=a$, and put $A=D\setminus\{n\}$. Call a residue modulo $L$ a hole if the rows of $A$ miss it. Among assignments on $A$ whose holes lie in one class modulo $n$, let $h$ be the minimum hole count. This minimum exists by coverage of $D$, and $h\ge1$ by irreducibility.

Choose any integer $b\ge1$, put $s=b+2$, $t=s+h-1$, and keep all rows of $A$. Add the following rows:

* At each level $1\le j\le t$, add a modulus $2^{a+j}$, except that at level $b$ use $2^b n$.
* At every level $s\le j\le t$, also add the modulus $2^j L$.

The enlarged period is $2^tL$ and belongs to the enlarged set $E$. Old rows have smaller binary valuation. Within each level that has two rows the odd part of $L$ distinguishes them. Indeed a distinct-modulus system consisting of powers of two has reciprocal sum less than one and cannot cover.

Choose an assignment realizing $h$. All its holes have a common residue modulo $2^a$, since $2^a\mid n$. Work on the $t$ new binary digits immediately above those $a$ low digits. At level $j$ let the first type of row take the binary pattern whose first one occurs at $j$, counting from the low end. Include the common old low bits, and at $b$ impose the common residue modulo $n$. These requirements are compatible by CRT. This covers every lift of every old hole with a nonzero new digit. Assign one second-type row to each of the $h$ old holes, fixing that old point and setting its first $j$ new bits to zero. All remaining lifts are covered.

Now consider **any** covering assignment on any subset of $E$. A fibre over one old point has $2^t$ elements. A level-$j$ row serves at most a $2^{-j}$ fraction of that fibre. If the projection modulo $n$ of the level-$b$ row misses an old hole, the available fraction is at most
$$
1-2^{-t}-2^{-b}+\sum_{j=s}^t2^{-j}<1,
$$
since $2^{1-s}<2^{-b}$. The same inequality applies if this row is absent. The retained old rows always have a hole because they lie in $A$. Hence the level-$b$ row is present, and all holes lie in its one $n$-class. Adding the corresponding old $n$-row would cover. Irreducibility of $D$ forces every row of $A$ to be present, and there are at least $h$ holes by the definition of $h$.

The first type alone can cover at most $1-2^{-t}$ of any fibre. Every old hole therefore needs a second-type row, each projecting onto just one old point. There are exactly $h$ available. All are needed and they serve distinct holes. Above the hole served by the last row, the second type supplies at most $2^{-t}$. Every first-type row is therefore needed there. This proves irreducibility with arbitrary reassignment after deletion.

## Reciprocal accounting

The increase in $\Phi$ is exactly $2^{-a}(1-2^{-t})$. The first-type mass agrees with that increase except for a loss $2^{-b}(2^{-a}-1/n)$ at the distinguished level. Excluding the final modulus of $E$ gives the exact identity
$$
S(E)-\frac1{2^tL}-\Phi(2^tL)
=S(D)-\frac1n-\Phi(L)
-2^{-b}\left(2^{-a}-\frac1n\right)
+\frac1L\sum_{j=s}^{t-1}2^{-j}.
$$
Let $b\to\infty$ with $D$ fixed. This proves $S(D)-1/n-\Phi(L)\le\Gamma$. Taking $n=N(D)$ and observing $N(D)=L$ on full-period sets gives the second characterization.

For the upper limit we need the uniform estimate
$$
\Phi(L)+2^{-a}\le R_0(k)+o(1)\qquad (|D|=k).
$$
Here $2^{-a}$ is exactly the whole missing tail of binary positions. For clarity, include the first binary position in the first-position knapsack even if $L$ is odd. The cost of the resulting first positions is at most $k$ by the Znám–Simpson bound $\sum_{p^j\mid L}(p-1)\le k-1$. Fill all higher positions in the upper bound by their absolutely convergent total. These operations account for the full missing binary tail at both odd and even $L$. The first positions have decreasing value-to-cost ratio $H_{p-1}/[p(p-1)]$, so the fractional maximum takes the primes in order. Its value plus the higher-position total equals $R_0(k)+o(1)$ by the [zero-defect estimate and knapsack argument](anchored.pdf). Allowing the single extra unit of cost at a growing cutoff changes that bound by $o(1)$, since the marginal value-to-cost ratio tends to zero.

Since $1/N(D)\le2^{-a}$, the finite characterization gives $R(k)\le R_0(k)+\Gamma+o(1)$ whenever $\Gamma$ is finite. For the lower limit, the full-period covers are available at all sufficiently large exact sizes by the [earlier transfer theorem](transfer.md). If $\Gamma=+\infty$, the same lower limit alone proves divergence.

## Periods of near maximizers when the excess is bounded

If $\Gamma$ is finite and $R(k)-S(D_k)\to0$, the periods of $D_k$ are eventually divisible by every fixed integer. For the binary part, $N(D)\ge3\cdot2^a$. When $a=0$ all moduli are odd and exceed one. When $a>0$ at least two distinct moduli have valuation $a$, since above any hole of the lower rows both top binary lifts need coverage. At least one of the two odd parts is then at least three. Thus the preceding upper bound leaves a gap of at least $(2/3)2^{-a}-o(1)$ below $R_0(k)+\Gamma$. This forces $a\to\infty$ for the stated near maximizers.

For fixed odd $p$ and $j\ge1$, if $p^j\nmid L$, its value $H_{p-1}/p^j$ is missing in addition to the binary tail. To charge it in the same upper estimate, include the missing term in the higher-position total when $j\ge2$, or allow the extra fixed first-position cost $p-1$ when $j=1$. This produces another fixed gap along any subsequence omitting $p^j$. The additive limit for $R(k)$ excludes every such subsequence.

## An example with four indispensable holes

Start with the irreducible set $2,3,4,6,12$. Replace $12$ by $5d$ for $d=1,2,3,4,12$. Then replace $60$ by $7d$ for $d=3,4,5,12,15,20,30$. Each replacement of a distinguished modulus $m$ uses a fresh prime $p$ and exactly $p$ cofactors dividing $m$ whose lcm is $m$. The new classes cover the old distinguished class using the $p$ different sections. Conversely at an ordinary hole every section requires a row, so all new rows are present, with a common projected intersection equal to a class modulo $m$. Contracting recovers the old cover and forces all ordinary rows. The five-modulus seed can also be checked directly modulo 12.

Here is a direct proof that four holes are necessary when $n=20$. The lower rows after deletion are $2,3,4,6,5,10,15$. The first four miss a class modulo 12 by irreducibility of the five-modulus seed. Its five lifts modulo 60 lose at most three points to the three multiples of 5. Take two surviving points $x,y$ congruent modulo 12. At most one belongs to the designated 20-class, since $\operatorname{lcm}(12,20)=60$. Rename an outside point $x$. Every lift of $x$ must be covered by a 7-row. Thus each 7-section gets exactly one row whose projected class contains $x$. The difference $y-x$ is a nonzero multiple of 12 modulo 60 and hence is nonzero modulo 5. The four cofactors $5,15,20,30$ must all miss $y$, leaving four distinct points above it.

For this size-15 set of period 420, take $n=20$. The exact minimum in the definition of $h$ is **four**. The [finite checker](binary-lift-check.py) enumerates ordinary holes modulo 60, retaining only inclusion-minimal masks. This pruning is valid since removing holes can only reduce the objective and weaken the common-class constraint. Translation normalizes the permitted 20-class to zero. The program partitions the seven indexed cofactors among seven labelled sections, allowing empty sections, and independently tries every projected residue in each assigned section. The minimum over all partitions and ordinary masks is four. A separate direct witness leaves exactly $40,100,160,340\pmod{420}$. With $b=1$ the resulting 24 distinct moduli cover all 26,880 residues in their period, checked separately by explicit residues. Irreducibility of this lift follows from the written argument. Reproduce with `python binary-lift-check.py`.

The finite construction and convergence argument are written proofs. The auxiliary finite computation checks the example. The logarithmic-order results of Star Fleet Math and Wouter van Doorn and the bounds of Öztürk concern the underlying [Erdős–Graham question](https://www.erdosproblems.com/1189). The theorem here concerns the additive excess around $R_0(k)$.
