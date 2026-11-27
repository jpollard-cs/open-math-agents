# Long intervals with negligible growth of the divisor count of a factorial

Jordan Pollard · November 27, 2026  
OpenAI Codex developed the argument and prepared this note.

Let $D(n)=\tau(n!)$, and let $K(n)$ be the least $k\ge1$ with $D(n+k)\ge2D(n)$. Every sufficiently large scale contains long intervals on which even the total logarithmic gain tends to zero. The argument uses an existing simultaneous-residue theorem behind the 2026 prime-gap bound and applies it to the offsets left over by a least-common-multiple construction.

## Result

For each fixed $B>0$ there is $c_B>0$ such that, for all sufficiently large integers $Y$ and every integer $X\ge Y$, some $n\in[X,X+Y]$ satisfies, with $H=\lfloor c_B(\log Y)(\log_2Y)/\log_3Y\rfloor$,
$$
0\le \log\frac{D(n+H)}{D(n)}\ll_B (\log_2Y)^{-B}.
$$
In fact at every $1\le i\le H$, the integer $n+i$ has a divisor strictly between $c'_B H(\log_2Y)^B$ and $\sqrt{n+i}$. Thus none of these integers is a prime times a positive cofactor at most $c'_B H(\log_2Y)^B$. Here $\log_j$ means $j$ iterations of the natural logarithm.

For every fixed $0<\rho<1$, one may choose $c_B=c_{B,\rho}>0$ so that every interval $[X,X+Y]$ contains at least $Y^{1-\rho}$ such starts. Taking $X=Y$, it follows that
$$
K(n)\gg\frac{(\log n)(\log_2 n)}{\log_3 n}
$$
for infinitely many $n$. The ratio of this scale to the scale $(\log n)(\log_2n)(\log_4n)/(\log_3n)^2$ in Freiberg's September 2026 theorem tends to infinity as $\log_3n/\log_4n$. This comparison concerns the lengths of the intervals. Erdős 420(i) asks for growth throughout much longer windows of length $(\log n)^C$ for some fixed $C>1$ and remains open. [Erdős, Graham, Ivić and Pomerance](https://math.dartmouth.edu/~carlp/factorial.pdf) · [Freiberg, Theorem 1.1](https://arxiv.org/abs/2609.15597)

## The simultaneous-residue input

There is an absolute $\delta>0$ with the following property. For every sufficiently large integer $x$, let $\mathcal P_x$ be the primes satisfying
$$
x^6<p\le\left\lfloor\exp\bigl(x/(\log x)^5\bigr)\right\rfloor .
$$
Let $I$ be a finite nonempty set with $|I|\le\delta x$. For each $p\in\mathcal P_x$, independently prescribe any injective map $r_p:I\to\mathbb Z/p\mathbb Z$. There is an integer $0\le t<\lfloor e^x\rfloor$ for which each $i\in I$ has some $p\in\mathcal P_x$ satisfying $t\equiv r_p(i)\pmod p$.

In the Lean namespace `LongGapsBetweenPrimes`, the lemma `eventually_simultaneous_roots` gives this statement. Its cutoffs are `sieveZ`, `sieveY` and `sieveT`. The argument in §4 of OpenAI's paper constructs these auxiliary prime factors in proving Proposition 1.2. The proposition's headline applies this to a primorial as the coefficient of the linear forms. We use the stated simultaneous-residue lemma itself, which allows arbitrary injective residue maps, so a different coefficient coprime to every auxiliary prime is permitted. The auxiliary factors are individually bounded from both sides. [OpenAI, §4, especially the conclusion of Proposition 1.2](https://cdn.openai.com/pdf/51126fac-1b68-4128-9666-c908bcc16033/long_gaps.pdf) · [Lean statement](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3480-L3486)

## Divisibility on most offsets

Fix $B>0$. Set
$$
h=\left\lfloor\epsilon\frac{x\log x}{\log_2x}\right\rfloor,
\qquad w=\lceil h(\log x)^B\rceil,
\qquad M=\operatorname{lcm}(1,2,\ldots,x),
$$
where the constant $\epsilon>0$ will be chosen small in terms of $B$ and $\delta$. An integer $m$ fails to divide $M$ precisely when some prime power $p^e>x$ divides $m$. We claim that, for some integer $A\in[w,2w]$, at most $\delta x$ of the offsets $1\le i\le h$ fail the test $A+i\mid M$.

In $[1,3w]$ the proportion, relative to $3w$, of integers divisible by a prime $p>x$ is at most
$$
\sum_{x<p\le3w}p^{-1}\ll\frac{1+\log(3w/x)}{\log x}.
$$
Dyadic subdivision and the elementary prime-counting upper bound $\pi(t)\ll t/\log t$ prove this inequality. The corresponding proportion for prime powers $p^e>x$, $e\ge2$, is $O(x^{-1/2})$. For $p\le\sqrt x$ sum the geometric tail starting with the first $p^e>x$, giving at most $2/x$ per prime. For $p>\sqrt x$ the tail from $e=2$ costs at most $2/p^2$. These bounds include all failures of divisibility by $M$.

Average over all integers $A\in[w,2w]$. Since $h\le w$, every exceptional $m=A+i$ lies in $[1,3w]$ and has at most $h$ representations. Thus the average number of exceptional offsets is
$$
\ll h\left(\frac{1+\log(3w/x)}{\log x}+x^{-1/2}\right).
$$
For sufficiently large $x$, $\log(3w/x)\le(B+2)\log_2x$, and the displayed bound is at most $C(B+3)\epsilon x+o(x)$ for an absolute $C$. Choose $\epsilon$ small enough and take a seed $A$ achieving at most the average. Write $I$ for its exceptional offsets. Every nonexceptional offset now has a fixed divisor $d_i=A+i>w$ of both $M$ and $n+i$ for every $n\equiv A\pmod M$.

## Giving the exceptional offsets large divisors

Fix $0<\rho<1$, choose $0<\theta<\rho/2$ and set $x=\lfloor\theta\log Y\rfloor$ and $T=\lfloor e^x\rfloor$. By the prime number theorem, $\log M=\psi(x)=(1+o(1))x$. Thus $MT=Y^{2\theta+o(1)}$. Split the possible starts $[X,X+Y]$ into disjoint blocks of $M(T+1)$ consecutive integers, discarding the final remainder. In each full block take its first member $N_0\equiv A\pmod M$. All $N_0+Mt$, $0\le t<T$, belong to that same block.

For every $p\in\mathcal P_x$, we have $p>x^6>h$ and $p\nmid M$. For each $i\in I$ prescribe
$$
r_p(i)=-(N_0+i)M^{-1}\pmod p.
$$
These roots are distinct modulo $p$ because the distinct offsets are in $[1,h]$. The simultaneous-residue theorem gives a single $t$ for which every $N_0+Mt+i$, $i\in I$, has some prime divisor $d_i\in\mathcal P_x$. If $I$ is empty, use $t=0$. Put $n=N_0+Mt$. We have $w<x^6$ and $3w<\sqrt Y$ eventually. Also $\exp(x/(\log x)^5)<\sqrt Y$. Consequently, both for the nonexceptional offsets and for the exceptional ones,
$$
w<d_i<\sqrt{n+i},\qquad d_i\mid n+i.
$$
This holds in each full block. The number of such blocks is $Y^{1-2\theta+o(1)}\ge Y^{1-\rho}$ eventually, uniformly for all $X\ge Y$.

## From a divisor certificate to the factorial ratio

For $m=n+i$ and a prime $p\mid m$, its contribution to $\log(D(m)/D(m-1))$ is
$$
\log\left(1+\frac{v_p(m)}{1+v_p((m-1)!)}\right)\le p v_p(m)/m .
$$
The inequality uses $1+v_p((m-1)!)\ge m/p$. For $p\le\sqrt m$, the function $t/\log t$ on $[2,\sqrt m]$ attains its maximum at the right endpoint for $m\ge16$. Thus $\sum_{p\mid m,\ p\le\sqrt m}p v_p(m)/m\le2/\sqrt m$. If $p>\sqrt m$ occurs, it is the unique such prime and its contribution is exactly $\log(1+1/s)$ for $s=m/p$. Since $p>d_i$, the divisor $d_i$ divides $s$. Hence $s>w$ and the contribution is at most $1/w$. Summing the $h$ inequalities gives
$$
0\le\log\frac{D(n+h)}{D(n)}\le\frac{2h}{\sqrt Y}+\frac hw\ll_B (\log x)^{-B}.
$$
For all sufficiently large $Y$, $h\ge\lfloor c_B(\log Y)(\log_2Y)/\log_3Y\rfloor$ with, for example, $c_B=c_{B,\rho}=\theta\epsilon/2$. Restrict to that shorter window. Taking $X=Y$ gives $n\le2Y$, so the asserted length in terms of $n$ follows. A ratio tending to one is eventually less than two, completing the proof.

## A limitation of covering by a fixed congruence class

Let $x\to\infty$ through positive integers, let $h=h(x)\to\infty$ be an integer, and take $w=w(x)\ge h$. Let $C>0$ be fixed. For every positive integer $M$ with $\log M\le Cx$ and every integer $A$, put $g_i=\gcd(A+i,M)$, $1\le i\le h$. A positive integer $d$ divides $n+i$ for every $n\equiv A\pmod M$ precisely when $d\mid g_i$ (subtract two consecutive elements of the progression). Thus the number $k$ of offsets at which this progression alone supplies no divisor exceeding $w$ equals $\#\{i:g_i\le w\}$. Uniformly in $M,A,h,w$,
$$
k\ \ge\ \frac{h\log(w/x)-O_C(h+x)}{\log w}.
$$
Indeed, count the offsets divisible by each prime power $p^j\mid M$. There are at most $h/p^j+1$, so
$$
\sum_{i=1}^h\log g_i
\le h\sum_{p^j\mid M}\frac{\log p}{p^j}+\log M
\le h(\log x+O_C(1))+Cx.
$$
For the last inequality, prime powers $p^j>x$ contribute at most $(\log M)/x$. Those at most $x$ contribute at most $\sum_{r\le x}\Lambda(r)/r=\log x+O(1)$, where $\Lambda(p^j)=\log p$ and $\Lambda$ vanishes on other integers. This estimate follows by counting prime powers in $\log(x!)=\sum_{r\le x}\Lambda(r)\lfloor x/r\rfloor$ and using $\sum_{r\le x}\Lambda(r)=O(x)$. At the $h-k$ covered positions $\log g_i>\log w$, which proves the claimed lower bound.

In particular, if $h/(x\log x/\log_2x)\to\infty$ then $k/x\to\infty$, even with $w=h$. To see this, first suppose $h\le x^2$. Then $\log h\le2\log x$ and $\log(h/x)\ge(1-o(1))\log_2 x$. For $h>x^2$ use $\log(h/x)\ge(\log h)/2$. The number of failures is nondecreasing in $w$, so the conclusion extends to every $w\ge h$. An arbitrary fixed progression with $\log M=O(x)$ followed by individual repairs at at most $O(x)$ offsets therefore cannot certify divisors exceeding $h$ throughout a longer window. This gives a limitation of the construction at the same order of magnitude as the theorem.

There is also a weighted version. If $I$ is a set of $k<h$ indices and $\sum_{i\notin I}1/g_i\le C'$ for a fixed $C'>0$, the arithmetic-geometric mean inequality gives
$$
(h-k)\log\bigl((h-k)/C'\bigr)\le\sum_{i\notin I}\log g_i\le h(\log x+O_C(1))+Cx.
$$
For $k=O(x)$ and $h/x\to\infty$, expand the left side as $h\log h-k\log h-O_{C'}(h+k)$ to obtain $h\log(h/x)\le k\log h+O_{C,C'}(h+x+k)$. The same two ranges for $h$ show that $h/(x\log x/\log_2x)\to\infty$ is impossible under this weighted certificate. A proof using additional information about prime factors of selected lifts could go beyond this obstruction.
