# The divisor count of a factorial over a full logarithmic window

Jordan Pollard · November 27, 2026  
OpenAI Codex developed the argument and prepared this note.

Write $D(n)=\tau(n!)$, $G(n,h)=\log(D(n+h)/D(n))$, and $\log_j$ for the $j$-fold iterated natural logarithm. For every $0<\rho<1$ and fixed $0\le a<1$, there are $d_\rho>0$ and, in every sufficiently large $[Y,2Y]$, at least $Y^{1-\rho}$ integers $n$ satisfying
$$
G\bigl(n,\lfloor(\log n)(\log_2 n)^a\rfloor\bigr)
\ll \exp\!\bigl(-d_\rho(\log_2 n)^{1-a}\bigr).
$$
In particular, at $a=0$ the ratio $D(n+\lfloor\log n\rfloor)/D(n)$ is $1+O((\log n)^{-d_\rho})$. Both the coefficient $1$ and the dependence on the selected start $n$ in this window length are literal.

## A bound uniform in the window length

There are $c_\rho,b_\rho>0$ such that for each sufficiently large integer $Y$, every integer $X\ge Y$, and every integer $h$ in the range
$$
\log Y\le h\le c_\rho\frac{(\log Y)(\log_2Y)}{\log_3Y},
$$
at least $Y^{1-\rho}$ integers $n\in[X,X+Y]$ satisfy
$$
G(n,h)\ll\exp\!\left(-b_\rho\frac{(\log Y)(\log_2Y)}h\right).
$$
The set of starts may depend on $h$.

Choose $0<\theta<\rho/2$ and put $x=\lfloor\theta\log Y\rfloor$, $M=\operatorname{lcm}(1,\ldots,x)$. We use the simultaneous-residue lemma in OpenAI's proof of a prime-gap theorem. For some absolute $\delta>0$ and all sufficiently large $x$, if $|I|\le\delta x$ and each auxiliary prime $x^6<p\le\lfloor\exp(x/(\log x)^5)\rfloor$ is given an injective family of residue classes $r_p(i)$ indexed by $i\in I$, then some $0\le t<\lfloor e^x\rfloor$ has, for each $i$, $t\equiv r_p(i)\pmod p$ for at least one auxiliary $p$. [Upstream Lean statement](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3480-L3486) · [OpenAI, Section 4](https://cdn.openai.com/pdf/51126fac-1b68-4128-9666-c908bcc16033/long_gaps.pdf)

Take a small absolute constant $0<\eta<1$ and define
$$
L=\frac{\eta x\log x}{h},\qquad w=\lceil x e^L\rceil.
$$
We have $h\ge x$. Choose $c_\rho$ sufficiently small that $h\le (\eta/4)x\log x/\log_2x$ throughout the displayed range. Then $\log(h/x)\le\log_2 x\le L/4$, so $h/w\le e^{-3L/4}$ and $h\le w\le2x^2$.

For some seed $A\in[w,2w]$, at most $\delta x$ offsets $i\le h$, $i\ge1$, satisfy $A+i\nmid M$. Indeed the proportion of integers up to $3w$ divisible by a prime $p>x$ is at most
$$
\sum_{x<p\le3w}\frac1p\ll\frac{1+\log(3w/x)}{\log x}\ll\frac{1+L}{\log x}.
$$
On each dyadic interval $(u,2u]$ with $u\ge x$, Chebyshev's prime-counting bound gives a sum $\ll1/\log x$. There are $O(1+\log(3w/x))$ such intervals, also when $w$ is a fixed power of $x$. Prime powers $p^j>x$, $j\ge2$, add a proportion $O(x^{-1/2})$. For $p\le\sqrt x$ the geometric tail starts below $1/x$; for $p>\sqrt x$ sum $2/p^2$. Each defective integer $m=A+i$ is counted in at most $h$ choices of $A$, so the mean number of defective offsets is at most
$$
C\left(\frac h{\log x}+\eta x+\frac h{\sqrt x}\right)
$$
for an absolute $C$. The first and last terms are $o(x)$ uniformly in $h$. Choose $C\eta<\delta/2$, then choose $c_\rho$ as above. This supplies the desired seed. For a nondefective offset and every $n\equiv A\pmod M$, the integer $A+i>w$ divides $n+i$.

Write $T=\lfloor e^x\rfloor$. In each block of $M(T+1)$ consecutive starts in $[X,X+Y]$, choose its first $N_0\equiv A\pmod M$. For every defective offset prescribe $r_p(i)=-(N_0+i)M^{-1}\pmod p$. These residues are distinct since $h<x^6<p$, and $p$ is coprime to $M$. The lemma gives $n=N_0+Mt$ in that block for which every defective $n+i$ has an auxiliary prime divisor. If there are no defects, take $t=0$. The prime number theorem gives $M(T+1)=\exp((2+o(1))x)$, so the number of full blocks is $Y^{1-2\theta+o(1)}\ge Y^{1-\rho}$. Every $n+i$ has a certified divisor $d_i$ with $w<d_i<\sqrt{n+i}$, since $3w$ and $\exp(x/(\log x)^5)$ are below $\sqrt Y$ eventually.

For $m=n+i$, each $p\mid m$ contributes at most $pv_p(m)/m$ to $G(m-1,1)$, by $1+v_p((m-1)!)\ge m/p$. For $p\le\sqrt m$, $p/\log p\le\sqrt m/\log\sqrt m$ for $m\ge16$, and $\sum_{p\mid m}v_p(m)\log p=\log m$. Thus all such primes together contribute at most $2/\sqrt m$. If $p>\sqrt m$ divides $m$, it is unique, its cofactor $s=m/p$ is divisible by $d_i$, and its contribution is exactly $\log(1+1/s)\le1/w$. Consequently
$$
G(n,h)\le 2h/\sqrt Y+h/w\ll e^{-3L/4}.
$$
Here $L\le\eta\log x$ and $h\ll x\log x$, so the first term is negligible uniformly. As $x\log x\sim\theta(\log Y)(\log_2Y)$, this proves the asserted envelope.

For the opening result set $X=Y$ and $h=\lceil(\log(2Y))(\log_2(2Y))^a\rceil$. For each fixed $a<1$ this lies in the allowed range eventually. Every selected $n\in[Y,2Y]$ has $\lfloor(\log n)(\log_2 n)^a\rfloor\le h$, and $G(n,\cdot)$ is nondecreasing. Uniformly over that dyadic interval, $(\log Y)(\log_2Y)/h=(1+o(1))(\log_2 n)^{1-a}$. Reduce $b_\rho$ by a fixed factor to obtain the stated $d_\rho$.

## Sum of prime factors

Let $S(m)=\sum_{p\mid m}v_p(m)p$ and $f(n)=\min\{j\ge1:\sum_{i=1}^{j}S(n+i)>n\}$, as in Freiberg's Proposition 1.2. At the same selected starts the estimates above give $S(n+i)/(n+i)\le2/\sqrt Y+1/w$: a prime above $\sqrt{n+i}$ contributes exactly $1/s$. Multiplying by $(n+i)/n\le1+h/Y$ and summing shows
$$
\frac1n\sum_{i=1}^{h} S(n+i)\ll\exp\!\left(-b_\rho\frac{(\log Y)(\log_2Y)}h\right).
$$
Take $h$ equal to the integer part of the upper endpoint of the range, and $X=Y$. The right side tends to zero, so $f(n)>h\gg_\rho (\log n)(\log_2n)/\log_3n$ at all these starts. The factor by which this length exceeds Freiberg's stated scale tends to infinity as $\log_3 n/\log_4 n$. [Freiberg, Proposition 1.2](https://arxiv.org/abs/2609.15597)
