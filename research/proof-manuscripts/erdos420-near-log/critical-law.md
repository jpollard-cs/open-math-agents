# How frequently does the divisor count of a factorial double in a short window?

Jordan Pollard, with OpenAI Codex assistance · November 27, 2026

Let $D(n)=\tau(n!)$ and choose the starting integer $n$ uniformly from $X\le n<2X$, where $X$ is an integer tending to infinity. Set $G=\log(D(n+h)/D(n))$ and let $h=h(X)$ be a positive integer. All logarithms are natural.

**Unconditional frequency.** For every $1\le h=o(\log X)$, the number of starts for which $D(n+h)\ge2D(n)$ is asymptotic to $Xh/\log X$. More generally, for a fixed ratio $r>1$, set $M=\lfloor1/(r-1)\rfloor$ and $H_M=\sum_{s=1}^M1/s$, including $H_0=0$. Then
$$
 \mathbb P\{D(n+h)/D(n)\ge r\}
    =H_M\frac h{\log X}+O_r\!\left(\frac{h^2}{(\log X)^2}\right).                                      \tag{1}
$$
The formula includes the thresholds $r=1+1/s$ exactly. In particular, a ratio strictly larger than 2 by a fixed amount has frequency $O_r((h/\log X)^2)$.

**Critical window under a prime-tuples hypothesis.** Suppose $h/\log X\to\lambda\in(0,\infty)$ and assume the uniform prime-tuples conjecture for affine forms stated below. Then
$$
 G\ \Longrightarrow\ Y_\lambda
   =\sum_{s\ge1}\log(1+1/s)N_s,
 \qquad N_s\text{ independent with }N_s\sim\operatorname{Poisson}(\lambda/s).
                                                                    \tag{2}
$$
The series is finite almost surely in value. Its distribution is continuous, and
$$
 \mathbb P(Y_\lambda\le u)\sim
 \frac{e^{-2\gamma\lambda}}{\Gamma(1+\lambda)}u^\lambda
 \qquad(u\downarrow0),                                               \tag{3}
$$
where $\gamma$ is Euler's constant. Thus (3) describes a limit taken first in $X$ and then in $u$. Erdős problem 420(i) asks for divergence at *every* sufficiently large start for a window $(\log n)^C$ with $C$ large. These frequency results leave that question open. [Problem statement](https://www.erdosproblems.com/420)

## 1. The contribution from a prime with small cofactor

Write $a_s=\log(1+1/s)$ and let $C_s=\pi((n+h)/s)-\pi(n/s)$ count the products $sp$ in the window with $p$ prime. For fixed $Q$ and $h=O(\log X)$ define $W_Q=\sum_{s\le Q}a_s C_s$. Uniformly for sufficiently large $X$ with $Q\le\sqrt X$,
$$
 0\le G-W_Q,\qquad
 \mathbb E(G-W_Q)\ll\frac{h}{Q\log X}+\frac{h}{\sqrt X}.            \tag{4}
$$

Indeed, each prime $p\mid m$ contributes
$$
 \log\!\left(1+\frac{v_p(m)}{v_p((m-1)!)+1}\right)
$$
to the log gain at the step $m$. If $p>\sqrt m$ and $m=sp$, its contribution is precisely $a_s$, since $v_p((m-1)!)=s-1$. The other primes together contribute at most $2/\sqrt m$. To check this, use $v_p((m-1)!)+1\ge m/p$, $\log(1+x)\le x$, and, for $m\ge16$ and $2\le p\le\sqrt m$, $p/\log p\le\sqrt m/\log\sqrt m$. Finally $\sum_{p\mid m}v_p(m)\log p=\log m$. This is the largest-prime principle underlying Theorem 2 of Erdős, Graham, Ivić and Pomerance. [Original paper](https://math.dartmouth.edu/~carlp/factorial.pdf)

A bounded cofactor $s\le Q$ gives $p>\sqrt m$ throughout the window. Each omitted product $sp\le3X$ contributes for at most $h$ different starts. For $Q<s\le\sqrt{3X}$, Chebyshev's bound gives $\pi(3X/s)\ll X/(s\log X)$. Since $a_s\le1/s$, summing over $s>Q$ proves (4). For fixed $s$, the prime number theorem gives
$$
 \mathbb E C_s
 =\frac hX\big(\pi(2X/s)-\pi(X/s)\big)+O(h^2/X)
 \sim\frac{h}{s\log X}.                                            \tag{5}
$$
The endpoint error counts at most $O(h)$ integers within distance $h$ of either endpoint, with at most $h$ starts apiece.

## 2. Sparse windows and a uniform upper sieve

Fix $Q$. Put $K_Q=\sum_{s\le Q} C_s$ and $\theta=h/\log X$. For $1\le h=O(\log X)$,
$$
 \mathbb E[K_Q(K_Q-1)]\ll_Q \theta^2.                               \tag{6}
$$

Consider two distinct labelled hits $(s,i),(t,j)$ for $s,t\le Q$, $1\le i,j\le h$, where $n+i$ and $n+j$ are the respective prime multiples. Equal offsets cannot occur for large $X$. The prime factor with cofactor at most $Q$ exceeds the square root, so its representation is unique. For $i\ne j$, choose the residue of $n$ modulo $L=\operatorname{lcm}(1,\ldots,Q)$, writing $n=Lm+r_0$. If either divisibility fails, that residue gives no hits. Otherwise the two forms are
$$
 A m+B,\quad A'm+B',\qquad
 A=L/s,\quad B=(r_0+i)/s,\quad A'=L/t,\quad B'=(r_0+j)/t.
$$
Their determinant is $L(j-i)/(st)$. For large $X$ the two primes both exceed $\max(L,2)$. A nonprimitive form has a fixed prime divisor at most $L$. Two primitive forms can cover a full residue field by their roots only at $p=2$. Thus inadmissible pairs produce no hits.

Ford's uniform upper sieve for prime tuples bounds the count of $m$ by
$$
 \ll_Q \frac X{\log^2 X}
 \left(\frac{|j-i|}{\varphi(|j-i|)}\right)^2 .
$$
The theorem's exceptional primes divide $AA'(AB'-A'B)$; outside primes dividing $L$ these all divide $j-i$. The bounded mean of the displayed arithmetic factor follows by setting $u_p=(1-1/p)^{-2}-1=O(1/p)$, expanding $\prod_{p\mid d}(1+u_p)$ over squarefree divisors and using $\prod_p(1+u_p/p)<\infty$. Thus the sum over distinct offsets is $O_Q(h^2)$. Summing over cofactors and the finitely many residues proves (6). [Kevin Ford, *Sieve Methods*, Theorem 2.5](https://ford126.web.illinois.edu/sieve2023.pdf)

To obtain the stated error uniformly, allow the cutoff $Q=\lceil1/\theta\rceil$ to grow. It satisfies $Q\le 2\log X$ eventually. For each ordered cofactor pair $s,t\le Q$, put $g=\gcd(s,t)$, $l=st/g$ and $B(v)=(v/\varphi(v))^2$. Compatible offsets satisfy $g\mid(j-i)$ and specify a single residue class modulo $l$. With this modulus the two slopes are $t/g,s/g$ and the determinant is $(j-i)/g$. Ford's bound on the interval for $m$ is
$$
 \ll \frac{X}{l\log^2 X}\, B(s)B(t)B(|j-i|/g),
$$
uniformly, since $l\le 4\log^2 X$, $\log(X/l)\sim\log X$ and $B(vw)\le B(v)B(w)$. Nonprimitive or inadmissible forms again contribute zero; any prime divisor of a slope is at most $Q$, whereas the primes being counted exceed $X/Q$. Each positive value of $|j-i|/g$ occurs for at most $2h$ ordered offset pairs. The bounded-mean estimate $\sum_{v\le h/g}B(v)\ll h/g$ proved above therefore gives an expected count of distinct pairs with these labels at most
$$
  O\!\left(\theta^2\frac{B(s)B(t)}{st}\right).
$$
This is zero when $g>h$. With each hit weighted by $a_s$, its expected ordered distinct-pair mass is consequently
$$
 \mathbb E\!\left[W_Q^2-\sum_{s\le Q}a_s^2 C_s\right]
 \ll\theta^2\left(\sum_{s\le Q}\frac{a_s B(s)}s\right)^2\ll\theta^2,  \tag{7}
$$
since $a_s\le1/s$ and $B(s)$ has bounded mean. Unlike an unweighted count of all small-cofactor pairs, this estimate has an absolute constant independent of $Q$.

For each fixed $M$, the prime number theorem with the usual $O(x/\log^2 x)$ error in $\pi(x)-x/\log x$ gives $\mathbb E C_s=\theta/s+O_M(\theta^2)$ for $1\le s\le M$, using $h\ge1$. Thus (6) and the first two Bonferroni bounds yield
$$
 \mathbb P\{K_M\ge1\}=\theta H_M+O_M(\theta^2).
$$
A hit with $s\le M=\lfloor1/(r-1)\rfloor$ contributes at least $a=\log r$. For the reverse inequality assume $K_M=0$, let $a'=a_{M+1}<a$, and put $b=(a+a')/2$. Eventually $Q>M$ when $\theta\to0$. Every jump of $W_Q$ has size at most $a'$, so its ordered distinct-pair mass is at least $W_Q(W_Q-a')$. On $W_Q\ge b$ this is at least $b(b-a')>0$, an event with probability $O_r(\theta^2)$ by (7). On $W_Q<b$ and $G\ge a$ the omitted tail is at least $a-b>0$, an event also costing $O_r(\theta^2)$ by (4) and the choice of $Q$. This proves (1), including $M=0$.

Equivalently, on compact subsets of $(0,\infty)$ the rescaled measures $\theta^{-1}\mathcal L(G)$ converge vaguely to $\sum_{s\ge1}s^{-1}\delta_{a_s}$. The threshold calculation also shows that, for fixed $r>1$ with $M\ge1$, all but $O_r(Xh^2/\log^2 X)$ of the starts attaining that ratio contain a prime multiple with cofactor at most $M$. For doubling these are precisely the starts explained by a prime in the window.

## 3. The hypothesis at the critical scale

For each fixed $k$, tuple of fixed positive integer slopes $A_1,\ldots,A_k$, and constant $B>0$, assume the following. For integer intercepts $|b_j|\le B\log T$ for which the forms $A_jm+b_j$ are pairwise nonproportional and admissible, uniformly as $T\to\infty$,
$$
 \#\{T\le m<2T:\ A_jm+b_j\text{ prime for every }j\}
   =(1+o(1))\frac{T}{(\log T)^k}\mathfrak S(\mathbf b),
 \quad
 \mathfrak S(\mathbf b)=\prod_p
 (1-\nu_p/p)(1-1/p)^{-k},
$$
where $\nu_p$ is the number of residues $m\pmod p$ on which at least one form vanishes. This fixed-slope version of the uniform Hardy–Littlewood conjecture for affine prime tuples allows unequal slopes. The single-cofactor case is Gallagher's conditional Poisson theorem. Kowalski developed analogous Poisson limits for prime patterns through averages of local factors. [Gallagher, *On the distribution of primes in short intervals*](https://www.cambridge.org/core/journals/mathematika/article/on-the-distribution-of-primes-in-short-intervals/DCE557AC8750333E68426FCEEC11858C) · [Kowalski, *Averages of Euler products, distribution of singular series and the ubiquity of Poisson distribution*](https://people.math.ethz.ch/~kowalski/singular-series-distribution.pdf)

## 4. Independent cofactor counts

Fix $Q$ and a vector of nonnegative orders $(k_s)_{s\le Q}$ of total degree $k\ge1$. In each class $n=Lm+r_0$, with $0\le r_0<L$, choose $k_s$ ordered, distinct integers
$$
 b\in (r_0/s,(r_0+h)/s]
$$
for label $s$. Each represents offset $i=sb-r_0$ and the form $(L/s)m+b$. These choices expand the conditional mixed falling moment $\mathbb E[\prod_s(C_s)_{k_s}\mid n\equiv r_0\pmod L]$. Discard tuples with coincident offsets across labels, since they cannot supply two prime hits. All remaining pairs of forms have nonzero determinant. The sampling interval for $m$ differs by $O(1)$ endpoints from $[X/L,2X/L)$; even summed over $O(h^k)$ tuples the resulting probability error is $O_Q(h^k/X)=o(1)$. An inadmissible tuple gives zero for all large $X$, since a fixed prime divisor from a nonprimitive form divides a slope, and for primitive forms a covering prime is at most $k$.

The mean of $\mathfrak S(\mathbf b)$ over all permitted tuples, normalized by the size of the full product box, is $1+o(1)$. Here are the details. Let $y=(\log h)/4$ and $P=\prod_{p\le y}p$. The prime number theorem gives $P\le h^{1/2}$ eventually. For independent uniform $b_j\pmod P$, the truncated product over $p\le y$ has mean exactly one. At each $p$, condition on a uniform $m\pmod p$. The events $A_jm+b_j\not\equiv0$ are then independent and have probability $1-1/p$, including at primes dividing some slopes. Average over $m$ and apply the Chinese remainder theorem. Each coordinate interval in the actual box has length comparable to $h$, so it represents every residue mod $P$ with relative discrepancy $O_Q(P/h)$. The truncated products are nonnegative. Their box mean is therefore $1+o(1)$. Repeated offsets within any labels or between labels occupy $O_{Q,k}(h^{k-1})$ tuples; deleting them changes this mean by $o(1)$ because the truncated product is $O_k((\log y)^k)$ by Mertens' estimate.

For each remaining tuple let $\Delta=(\prod_j A_j)\prod_{i<j}(A_i b_j-A_j b_i)$. Its magnitude is between $1$ and $O_{Q,k}(h^{k(k-1)/2})$. For $p>y$ the local factor is $1+O_k(p^{-2})$ if $p\nmid\Delta$ and $1+O_k(p^{-1})$ otherwise. The entire tail is $1+o(1)$ uniformly, since
$$
 \sum_{p\mid\Delta,\ p>y}\frac1p
 \le\frac{\log|\Delta|}{y\log y}=o(1).
$$
This also handles tuples with a zero truncated product, whose full product vanishes. It proves the asserted mean.

The full product box has size $(1+o(1))\prod_s(h/s)^{k_s}$. Apply the conjecture with $T=X/L$, use $\log T\sim\log X$, and then average over the finitely many $r_0$. The mixed falling moments converge to $\prod_s(\lambda/s)^{k_s}$. These are the moments of independent Poisson variables, which are jointly moment-determinate by their exponential moments. Consequently $W_Q\Rightarrow\sum_{s\le Q}a_sN_s$. The expectation of the omitted part in (4) is $O_\lambda(1/Q)+o(1)$, and $\sum_{s>Q}a_s\mathbb EN_s=O_\lambda(1/Q)$. Letting $Q\to\infty$ proves (2). In particular $\mathbb E Y_\lambda=\lambda\sum_s a_s/s<\infty$.

## 5. Continuity and the lower tail

The terms with labels $s=p-1$ for primes $p$ already force continuity. For any finite set of distinct primes, $\log(p/(p-1))$ are rationally linearly independent. In any integer relation after exponentiation, the largest prime divides no smaller numerator and no denominator. Its valuation forces its coefficient to vanish, and induction finishes. For $p>1+\lambda$, the Poisson variable of mean $\lambda/(p-1)$ has mode zero. The largest atom of the contribution from any finite set $S$ of these primes is therefore $\exp(-\lambda\sum_{p\in S}1/(p-1))$. Adding the independent remainder cannot increase the largest atom. The reciprocal sum over primes diverges, so $Y_\lambda$ has no atoms.

For $t>0$ its Laplace transform is
$$
 L(t)=\mathbb E e^{-tY_\lambda}=\exp(-\lambda U(t)),\qquad
 U(t)=\sum_{s\ge1}\frac{1-e^{-t a_s}}s.
$$
Replacing $a_s$ by $1/s$ changes $U(t)$ by $O(1/t)$ as $t\to\infty$. Indeed $1/(2s)\le a_s\le1/s$ and $1/s-a_s\le1/(2s^2)$. The absolute difference is at most $(t/2)\sum_{s\ge1}s^{-3}e^{-t/(2s)}=O(1/t)$, by splitting into dyadic intervals about $t$. Subtract $H_{\lfloor t\rfloor}$ from the modified sum. It becomes a Riemann sum of mesh $1/t$ for $(1-e^{-1/v}-\mathbf1_{v\le1})/v$ on $0<v<\infty$. The exponential decay at zero and the $O(v^{-2})$ tail justify passage to the integral. Substitution $u=1/v$ gives the classical Euler-constant integral
$$
 \int_0^1\frac{1-e^{-u}}u\,du-\int_1^\infty\frac{e^{-u}}u\,du=\gamma .
$$
Since $H_{\lfloor t\rfloor}=\log t+\gamma+o(1)$, we have $L(t)\sim e^{-2\gamma\lambda}t^{-\lambda}$.

For completeness, tilt the law by the probability density $e^{-tY_\lambda}/L(t)$ relative to its original law. Under this tilt, $tY_\lambda$ has Laplace transform $L((1+v)t)/L(t)\to(1+v)^{-\lambda}$ for $v\ge0$. It thus converges in distribution to $\operatorname{Gamma}(\lambda,1)$. The bounded test function $e^u\mathbf1_{0\le u\le1}$ has no discontinuity of positive mass under that limit, and its tilted expectation is $\mathbb P(Y_\lambda\le1/t)/L(t)$. The limiting expectation is $\int_0^1u^{\lambda-1}\,du/\Gamma(\lambda)=1/\Gamma(1+\lambda)$. This proves (3).

## 6. All superlogarithmic window lengths under the same hypothesis

Write $\kappa=\sum_s a_s/s$ and $V=\sum_s a_s^2/s$. Assume the fixed-slope hypothesis of Section 3. If $h/\log X\to\infty$ and $h\le X$, then
$$
 \mathbb E\left|\frac{G(n,h)}{h/\log X}-\kappa\right|\longrightarrow0. \tag{8}
$$
In particular the log gain tends to infinity for a proportion tending to one of the starting integers. The hypothesis still concerns only shifts bounded by fixed multiples of $\log X$.

Fix $M>0$ and put $B=\lfloor M\log X\rfloor$. On each dyadic range $[X,2X)$ and $[2X,4X)$, (2) gives $G(n,B)\Rightarrow Y_M$. Equations (4) and (5), first with finite $Q$ and then with $Q\to\infty$, give convergence of its mean to $M\kappa$. Nonnegativity implies uniform integrability and hence convergence of the mean absolute deviation from $M\kappa$. By independence in (2), $\operatorname{Var}(Y_M)=MV$. Thus the limiting mean of $|G(n,B)/M-\kappa|$ on either dyadic range is at most $\sqrt{V/M}$.

Write $h=qB+d$ with $0\le d<B$. The log gain adds over the $q$ consecutive full blocks and the remainder. For every block $j$, the interval of translated starts $[X+jB,2X+jB)$ lies inside $[X,4X)$. Its mean absolute deviation is therefore bounded by the sum of the two dyadic means above, weighted by $1$ and $2$. This bound holds simultaneously in $j$, without any independence requirement. The remainder contributes at most one extra full block by monotonicity, with mean $O_M(1)$ by (4) and (5) on the same two ranges. Finally $qM/(h/\log X)\to1$ with $M$ fixed. The triangle inequality gives a limit superior in (8) at most $3\sqrt{V/M}$. Sending $M\to\infty$ proves the claim.
