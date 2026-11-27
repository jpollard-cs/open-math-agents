# A largest-prime-factor criterion for Erdős 420(i)

Jordan Pollard · November 27, 2026  
OpenAI Codex developed the argument and prepared this note.

Let $D(n)=\tau(n!)$, $G(n,h)=\log(D(n+h)/D(n))$, $h_C(n)=\lfloor(\log n)^C\rfloor$, and let $P(m)$ be the largest prime factor of $m>1$. Erdős 420(i) asks whether $G(n,h_C(n))\to\infty$ for some fixed $C>0$. The following criterion combines the single-hit reduction and the exact binomial cutoff in our earlier notes. The long intervals in the companion paper yield an obstruction at a smaller scale. [Problem statement](https://www.erdosproblems.com/420) · [Erdős, Graham, Ivić and Pomerance, Theorem 2](https://math.dartmouth.edu/~carlp/factorial.pdf)

**Proposition.** The following assertions are equivalent.

1. Erdős 420(i) holds.
2. Some fixed $A,B>0$ satisfy this condition for all sufficiently large $n$: among $n+1,\ldots,n+h_B(n)$ there is a number $sp$ with $p$ prime and $s\le h_A(n)$.
3. Some fixed $A,B>0$ satisfy, for every sufficiently large $n$,
   $$
   P\!\binom{n+h_B(n)}{h_B(n)}>\frac{n}{h_A(n)}.
   $$

A positive answer at exponent $C$ implies assertions 2 and 3 with $A=B=C$. Either assertion at exponents $(A,B)$ implies, for every $C>A+B$,
$$
G(n,h_C(n))\gg_{A,B,C}(\log n)^{C-A-B}.
$$

**Proof.** If $m=sp$ with $p>\sqrt m$, the contribution of $p$ to $\log(D(m)/D(m-1))$ is exactly $\log(1+1/s)$, since $v_p((m-1)!)=s-1$ and $v_p(m)=1$. For $m\ge16$, all prime factors $p\le\sqrt m$ together contribute at most $2/\sqrt m$. Indeed, each contribution is at most $p v_p(m)/m$, and the maximum of $t/\log t$ on $[2,\sqrt m]$ is attained at the right endpoint. Summing $v_p(m)\log p$ gives $\log m$.

In particular, if $1\le S\le\sqrt n$ and $(n,n+h]$ contains no prime multiple $sp$ with $s\le S$, then
$$
G(n,h)\le h\log\left(1+\frac1{S+1}\right)+\frac{2h}{\sqrt n}.
\tag{1}
$$
For $S=h=h_C(n)$ the right side is at most $1+o(1)$. This proves assertion 2 from assertion 1.

For the reverse direction let $b=h_B(2n)$, $S=h_A(2n)$ and $h=h_C(n)$. Partition the first $b\lfloor h/b\rfloor$ offsets into consecutive blocks of length $b$. Their initial points $x$ are at most $2n$ for large $n$, so each block contains a hit from assertion 2 with cofactor at most $S$. Since $S^2<n$, every such prime exceeds the square root of its multiple. Distinct blocks contribute at distinct steps, giving the explicit bound
$$
G(n,h)\ge \left\lfloor \frac hb\right\rfloor\log(1+1/S).
\tag{2}
$$
This yields the claimed rate.

For any positive integers $n,h,S$ with $hS\le n$, the following finite equivalence is exact:
$$
\bigl(\exists\, 1\le i\le h,\;1\le s\le S,\;p\text{ prime}: n+i=sp\bigr)
\quad\Longleftrightarrow\quad P\!\binom{n+h}{h}>n/S.
\tag{3}
$$
A hit gives $p>n/S\ge h$, so its prime factor survives division of the numerator product by $h!$. Conversely, a prime $p>n/S$ dividing the binomial divides some $n+i$. The inequalities $Sp>n$ and $p>h$ give $(S+1)p>n+h$, hence the integral cofactor is at most $S$. Since $h_A(n)h_B(n)=o(n)$, (3) proves the equivalence of assertions 2 and 3. $\square$

**Obstruction from long intervals.** Write $L_j=\log_j Y$. The companion construction gives, for every fixed $b>0$, constants $c_b,d_b>0$ and $Y^{1/2-o(1)}$ or more starts in each $[X,X+Y]$, $X\ge Y$, for which the window of length
$$
h=\lfloor c_b L_1L_2/L_3\rfloor
$$
contains no product $sp$ with $s\le S=\lfloor d_b h L_2^b\rfloor$. Here $hS=o(Y)$, so at every one of these starts
$$
P\!\binom{n+h}{h}\le n/S.
\tag{4}
$$
This gives an upper bound for the largest prime factor of a binomial coefficient at every certified start, including starts arbitrarily far to the right of $Y$. Assertion 3 asks whether there are exponents for which the reverse strict inequality holds at every large start. [Companion proof](large-jump.md)

**What a counterexample would imply for consecutive prime gaps.** Part (i) fails exactly when, for every fixed $a,b>0$, there are arbitrarily large $n$ for which all the intervals
$$
\left(\frac ns,\frac{n+h}{s}\right],\qquad
1\le s\le S=h_a(n),\qquad h=h_{a+b+1}(n),
$$
are simultaneously free of primes. Indeed a prime in the $s$-th interval gives precisely a hit with that cofactor. Failure of assertion 2 supplies such starts. Conversely, given any proposed exponents $A,B$, take $a=A$ and $b\ge B$ to rule out assertion 2 for those exponents.

Each indicated prime-free interval has length at least $(\log n)^b$ eventually. They occupy **distinct** consecutive-prime gaps: between the $s+1$ and $s$ intervals is a separation of length $(n-sh)/(s(s+1))\gg n/(\log n)^{2a}$. The prime number theorem with its classical logarithmic-power error, applied at the two endpoints, puts a prime in every separation for large $n$. Thus failure would force arbitrarily many polylogarithmically long prime gaps of specified sizes and positions at the same starting integer.

**Prior formulations.** The exact cutoff (3) and the symmetric case $A=B$ of the single-hit reduction already appeared in our earlier project notes. The classical observation that every prime greater than $h$ dividing the interval product survives in the binomial coefficient is also recorded by Shorey and Tijdeman. A separate working report treats the equivalent weighted prime count for each fixed exponent. [Shorey and Tijdeman, §1.4](https://pub.math.leidenuniv.nl/~tijdemanr/shoretij.pdf) · [Erdős Problem a Day, §4.1](https://www.erdosproblemaday.com/report/420)
