# Almost no factorial divisor growth on long intervals near the logarithmic scale

Jordan Pollard · November 27, 2026  
OpenAI Codex developed the argument and prepared this note.

Write $D(n)=\tau(n!)$, where $\tau$ counts positive divisors, and put
$$
G(n,H)=\log\frac{D(n+H)}{D(n)}.
$$
Erdős problem 420(i) asks whether $G(n,\lfloor(\log n)^C\rfloor)$ tends to infinity at every sufficiently large start for some fixed $C$. Erdős, Graham, Ivić and Pomerance constructed long intervals on which the ratio stays below two. We adapt their residue-class covering and averaging method to quantify how often the ratio can be arbitrarily close to one. The estimates below hold in every translated interval of starting integers. All logarithms are natural. [Problem statement](https://www.erdosproblems.com/420) · [Erdős, Graham, Ivić and Pomerance, *On the number of divisors of n!*, Theorem 3 and its proof, pp. 6–8](https://math.dartmouth.edu/~carlp/factorial.pdf)

Tristan Freiberg's September 2026 preprint proves a longer lower bound for the first doubling time $K(n)$ on a sequence of starts. Its length has order $\log n\,\log_2 n\,\log_4 n/(\log_3 n)^2$, gaining a factor of $\log_3 n$ over the 1996 bound. His proof allows some offsets to remain uncovered and shows that a positive fraction of the lifts in a chosen residue class have bounded total prime-factor mass. The theorem below instead provides an explicit rate at which the ratio approaches one, excludes an entire growing range of prime cofactors at each selected start, and works uniformly when the interval of starting integers is translated. [Freiberg, *Long runs of integers with small prime factors and the divisor function of n!*, Theorem 1.1, Proposition 1.2 and Section 5](https://arxiv.org/abs/2609.15597)

## Theorem

Fix $a\ge0$, $b>0$ and $\kappa>0$ with $a+b+\kappa<1$. For large integers $Y$, set $L=\log Y$, $V=\log L$ and $H=\lfloor L V^a\rfloor$. There is a constant $C=C(a,b,\kappa)>0$ such that, for every integer $X\ge Y$, at least
$$
Y\exp\!\left(-C\frac{\log Y}{(\log\log Y)^\kappa}\right)
$$
integers $n\in[X,X+Y]$ satisfy both properties below.

1. For $1\le i\le H$, the integer $n+i$ has no representation $sp$ with $p$ prime and $1\le s\le\exp(V^b)$.
2. The logarithmic gain satisfies $0\le G(n,H)\le\exp(-V^b)$.

In particular $D(n+H)/D(n)=1+O(\exp(-V^b))$ at these starts. Taking $X=Y$ gives $Y^{1-o(1)}$ starts in $[Y,2Y]$. The lower bound for their proportion may tend to zero. For $X$ much larger than $Y$, the stated length $H$ is measured in terms of $Y$.

For example, take $(a,b,\kappa)=(1/2,1/4,1/8)$. In every such interval one can take $H=\lfloor\log Y\sqrt{\log\log Y}\rfloor$. At least $Y\exp(-C\log Y/(\log\log Y)^{1/8})$ starts have logarithmic gain at most $\exp(-(\log\log Y)^{1/4})$. The lengths here are smaller than $(\log Y)^{1+\delta}$ for every fixed $\delta>0$.

## A covering by moderately large primes

Put $u=2L/V^\kappa$ and $d=a+\kappa$. Choose $b'>b$ and $\eta>0$ with $d+b'+\eta<1$. Define
$$
y=\exp((\log u)^{b'}),\qquad z=\exp((\log u)^{1-\eta}),\qquad
M=\prod_{y\le p\le u}p .
$$
We have $H\asymp u(\log u)^d$, $\log u\sim V$ and $\log M=O(u)$. We construct an integer $A$ modulo $M$ so that every $A+i$, $1\le i\le H$, shares at least one prime divisor with $M$.

First prescribe $A\equiv0\pmod p$ at all primes $z<p\le u/2$. An uncovered offset is either $z$-smooth, meaning that all its prime factors are at most $z$, or has a prime factor greater than $u/2$. For $\sigma=1-1/\log z$, the number of smooth offsets is at most
$$
H^{\sigma}\prod_{p\le z}(1-p^{-\sigma})^{-1}
\le H\exp\!\left(-\frac{\log H}{\log z}+O(\log\log z)\right).
$$
Indeed $p^{-\sigma}\le e/p$ and $\sigma\ge3/4$ eventually, so the logarithm of the product is $O(\sum_{p\le z}1/p)$. Since $\log H/\log z\asymp(\log u)^\eta$, this is $O_T(H/(\log u)^T)$ for each fixed $T>0$. The offsets with a prime divisor $q>u/2$ number at most $H\sum_{u/2<q\le H}1/q\ll H\log\log u/\log u$. To see the last bound, subdivide into dyadic intervals. Each contributes $O(1/\log u)$ by the elementary upper bound for the prime-counting function, and $H/u$ is at most a fixed power of $\log u$.

For every prime $y\le p\le z$, choose the residue for $-A$ modulo $p$ containing the largest number of surviving offsets. At most a fraction $1-1/p$ survives at that step. Mertens' product theorem gives $\prod_{y\le p\le z}(1-1/p)\ll\log y/\log z$. There are now at most
$$
O\!\left(u(\log u)^{d+b'+\eta-2}\log\log u\right)=o(u/\log u)
$$
uncovered offsets. There are $\gg u/\log u$ unused primes in $(u/2,u]$. Assign a different one to each remaining offset, prescribing $A\equiv-i$ modulo that prime. Choose residues arbitrarily for any unused primes. The Chinese remainder theorem gives the required $A$.

All starts $n\equiv A\pmod M$ obey property 1 for sufficiently large $Y$. Indeed, a prime $r\in[y,u]$ divides $n+i$. If $n+i=sp$ with $s<y$ and $p$ prime, then $r\nmid s$ and $p=r\le u$, whereas $n+i\ge Y>uy$. Finally $y>\exp(V^b)$ for large $Y$.

## Averaging the logarithmic gain in the covering class

Let $Q=\lfloor u^3\rfloor$. Uniformly in $n\ge Y$,
$$
G(n,H)\le \frac H Q+\frac{2H}{\sqrt Y}+
\sum_{s\le Q}\frac{1}{s}\#\{i\le H:n+i=sp,\ p\ \text{prime},\ 1\le i\}.
\tag{1}
$$
For a single step $m=n+i$, the prime $p\mid m$ contributes $\log(1+v_p(m)/(1+v_p((m-1)!)))$. Since $1+v_p((m-1)!)\ge m/p$, its contribution is at most $p v_p(m)/m$. For $2\le p\le\sqrt m$ and large $m$, one has $p/\log p\le\sqrt m/\log\sqrt m$. Summing $v_p(m)\log p$ over these primes bounds their contribution by $2/\sqrt m$. At most one prime $p>\sqrt m$ can divide $m$. Then $m=sp$ with $s<p$, and $v_p((m-1)!)=s-1$, so its contribution is exactly $\log(1+1/s)\le1/s$. This proves (1).

Let $J=Y/M$ and $B=M/\varphi(M)$. The class contains $J+O(1)$ starts in $[X,X+Y]$, and Mertens' theorem gives $B\ll\log u/\log y$. For $s\le Q$, let $N(s)$ count pairs $(i,n)$ in (1) over those starts. An occurrence forces $s\ge y$, since $X/Q>u$ for all sufficiently large $Y$. Write $g=(s,M)$, $k=s/g$ and $m_0=M/g$. There are at most $H/g+1$ eligible offsets, since $i\equiv-A\pmod g$. At a fixed eligible offset, the candidate primes $p$ occupy one residue class modulo $m_0$, because $kp\equiv(A+i)/g\pmod{m_0}$ and $(k,m_0)=1$. If this class is noncoprime to $m_0$, a prime in it would divide $M$ and be at most $u$, which has already been excluded.

The interval of possible primes has length $Y/s$, with arbitrary lower endpoint. To handle endpoint conventions we may enlarge its length to $Y/s+2$. The ratio of the original length to $m_0$ is $J/k$. Since $\log M=o(\log Y)$ and $Q$ is polylogarithmic in $Y$, we have $\log(J/k)\asymp\log Y$ uniformly. The short-interval Brun–Titchmarsh inequality therefore bounds the prime count for one offset by
$$
\ll \frac{Y/s}{\varphi(m_0)\log Y}
\le \frac{J}{k}\frac{B}{\log Y}.
$$
This uses an upper bound uniform in the location of the interval, which is essential when $X$ can be arbitrarily large compared with $Y$. [Short-interval Brun–Titchmarsh inequality, Lemma A.4](https://ems.press/content/serial-article-files/39116)

After summing offsets we get $N(s)\ll J B(H+g)/(s\log Y)$, and hence also the slightly weaker bound with $\varphi(s)$ in place of $s$ in the denominator. Two inverse-totient estimates suffice to sum this latter bound:
$$
\sum_{s\ge y}\frac1{s\varphi(s)}\ll \frac1y,\qquad
\sum_{s\ge1}\frac{(s,M)}{s\varphi(s)}\ll B .
\tag{2}
$$
For the first, $s/\varphi(s)=\sum_{r\mid s}\mu^2(r)/\varphi(r)$, so $\sum_{s\le T}s/\varphi(s)\ll T$ by the convergent Euler product $\sum_r\mu^2(r)/(r\varphi(r))=\prod_p(1+1/(p(p-1)))$. Summation on dyadic intervals gives the claim. For the second, use $(s,M)=\sum_{r\mid(s,M)}\varphi(r)$, write $s=rv$, and use $\varphi(rv)\ge\varphi(r)\varphi(v)$. The sum is at most $\sum_{r\mid M}r^{-1}\sum_{v\ge1}(v\varphi(v))^{-1}\ll B$.

Averaging (1) and applying (2) gives
$$
\frac{1}{J+O(1)}\sum_{\substack{X\le n\le X+Y\\ n\equiv A\ ({\rm mod}\ M)}}G(n,H)
\ll \frac H Q+\frac{2H}{\sqrt Y}
       +\frac{B}{\log Y}\left(\frac H y+B\right).
\tag{3}
$$
Here $H/Q\ll V^{a+3\kappa}/L^2$, $B\ll V$ and $y=\exp((1+o(1))V^{b'})$. Each term in (3) is $o(\exp(-2V^b))$ because $b<b'<1$. Markov's inequality shows that a proportion $1-o(1)$ of the starts in this class has $G(n,H)\le\exp(-V^b)$. All error estimates are uniform in $X\ge Y$. We have $J=Y\exp(-O(L/V^\kappa))$, proving the theorem.

## How close the exceptional intervals can be

Let $N$ be large, $N\le X\le2N$, and $Y=\lceil\exp(\log N/(\log\log N)^\kappa)\rceil$. Every $[X,X+Y]$ contains $Y^{1-o(1)}$ starts with
$$
G\bigl(n,\lfloor\log n\,(\log\log n)^a\rfloor\bigr)
\le\exp\bigl(-(\log\log n)^b\bigr).
$$
Indeed choose $a_1>a+\kappa$, $b_1>b$ and $\kappa_1>0$ with $a_1+b_1+\kappa_1<1$ and apply the theorem at $(a_1,b_1,\kappa_1)$. Here $\log\log Y\sim\log\log N$ and $n\le3N$, so the larger exponents absorb the fixed endpoint constants. The same starts lack prime multiples with cofactors up to $\exp((\log\log n)^b)$ throughout the indicated window.

## A longer window from the published covering

Define $R(v)=v\log v\,\log_3 v/(\log_2 v)^3$, where $\log_j$ denotes the $j$-fold iterated logarithm. Fix $0<c<1/2$ and $\epsilon>0$. For every sufficiently large $Y$ and all $X\ge Y$, the interval $[X,X+Y]$ contains $\gg_{c,\epsilon}Y^{1-2c-\epsilon}$ starts $n$ with $G(n,\lfloor cR(\log Y)\rfloor)=o_Y(1)$, uniformly in $X$. Equivalently one may bound $G$ on these starts by a single positive function of $Y$ that tends to zero.

For this version use the covering proved by Erdős, Graham, Ivić and Pomerance on pp. 6–7. For each fixed $e>0$ and sufficiently large $u$, their primes $[(\log u)^2,u]$ cover every offset up to $(1/2-e)R(u)$. Choose $2c<\alpha<\min(1,2c+\epsilon)$, take $u=\alpha\log Y$, and then choose $e$ with $(1/2-e)\alpha>c$. Since $R(u)\sim\alpha R(\log Y)$, this covers the required $H=\lfloor cR(\log Y)\rfloor$. Use $y=(\log u)^2$, $Q=\lfloor u^3\rfloor$ and $B\ll\log u/\log_2 u$. The prime number theorem gives $M=Y^{\alpha+o(1)}$, whence $\log(J/k)\gg_\alpha\log Y$ for all $k\le Q$. The proof of (3) now gives an average tending to zero. In particular its term $BH/(y\log Y)$ is $O(\log_3 u/(\log_2 u)^4)$. By Markov's inequality, a proportion $1-o(1)$ of the $Y^{1-\alpha+o(1)}$ available starts has gain $o(1)$, as claimed. The covering is taken directly from their proof. The translation and count of starts follow by choosing the modulus relative to $Y$ and keeping the average over the residue class.
