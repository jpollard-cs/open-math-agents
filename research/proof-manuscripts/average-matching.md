# Distinct multiples in a typical interval

For positive integers $n$ and nonnegative integers $m$, let $f(n,m)$ be the least integer $H$ for which $(m,m+H]$ contains distinct integers $x_1,\dots,x_n$ with $k\mid x_k$ for every $1\le k\le n$. Set $L=\operatorname{lcm}(1,\dots,n)$. Translating every $x_k$ by $L$ shows that $f(n,m)$ is periodic in $m$ modulo $L$.

Erdős and Pomerance proved that the mean of $f(n,m)$ over this period is at most $n^{1+o(1)}$. At the end of Section 5 of their 1980 paper, they asked for an upper bound $O(n(\log n)^\gamma)$ with some fixed $\gamma>0$. The theorem below gives that estimate for every fixed $\gamma>2$. It matches every integer from 1 through $n$ simultaneously. The maximum over all starts appearing in Erdős problem 711 is a separate question. The catalog uses an open right endpoint, which adds one to the integer minimum. [Erdős and Pomerance, pp. 147, 158](https://math.dartmouth.edu/~carlp/PDF/matching.pdf) · [Problem 711](https://www.erdosproblems.com/711)

## The period average and its upper tail

Write $\log_j$ for the $j$-fold iterate of the natural logarithm. For sufficiently large $n$, put
$$
 B(n)=n(\log n)^2\frac{\log_2 n}{\log_3 n}.
$$

**Theorem.** For every fixed $A>0$ there is a constant $C_A$ for which
$$
 \frac{1}{L}\#\{0\le m<L:f(n,m)>C_A B(n)\}\ll_A n^{-A}.
$$
In particular,
$$
 \frac1L\sum_{m=1}^L f(n,m)\ll B(n).
$$

### A matching from rough cofactors

Put $P=\prod_{p\le n}p$, the product over primes. For an integer $t\ge1$, let $b_n(t)$ be the fraction of residues $q\bmod P$ for which none of $q+1,\dots,q+t$ is coprime to $P$. We claim that
$$
 \Pr_{m\bmod L}\{f(n,m)>nt\}\le n b_n(t). \tag{1}
$$

Take $m$ uniformly from $0,\dots,LP-1$. Fix a row $k\le n$. Because $kP\mid LP$, the quotient $q=\lfloor m/k\rfloor$ is uniform modulo $P$ because each quotient residue occurs exactly $k$ times in a block of $kP$ consecutive starts beginning at a multiple of $kP$. If $\gcd(q+j,P)=1$ for some $1\le j\le t$, choose $x_k=k(q+j)$. Then $m<x_k\le m+kt$. Moreover,
$$
 \gcd(x_k,L)=k\gcd(q+j,L/k)=k .
$$
The prime divisors of $L/k$ all divide $P$. Consequently the value of $x_k$ determines its row $k$, and choices made for different rows are always distinct. Each row has failure probability $b_n(t)$, so a union bound gives (1) on the enlarged period. The event on the left side has period $L$, which gives (1) as stated.

### Applying the random sieve

For each prime $p\le z$, independently choose one forbidden residue uniformly modulo $p$. Write $S_z$ for the set of integers lying in none of the forbidden classes. The Chinese remainder theorem identifies the residues $-q\bmod p$, for $q$ uniform modulo $P$, with exactly this distribution at $z=n$. By translation invariance, $b_n(t)=\Pr\{S_n\cap[0,t-1]=\varnothing\}$.

We use the following consequence of Banks, Ford and Tao. For every sufficiently large $x$ there exist $z=x^{e^{-\gamma_E}+o(1)}$, with $\gamma_E$ Euler's constant, and an integer $y$ for which
$$
 y\ll(\log x)^2\frac{\log_2 x}{\log_3 x},
 \qquad
 \Pr\{S_z\cap[0,y]=\varnothing\}\ll x^{-1}. \tag{2}
$$
For the specific single-interval bound, fix a sufficiently small positive constant $\varepsilon$ in their proof of Theorem 7.1. Their choice is $y=g((1+\varepsilon)\xi(\log(x^2))^2)$, rounded up if necessary, where $g,\xi$ are as defined in that paper. Equation (1.14) gives the displayed upper bound for $y$, and (1.7) gives the size of $z$. In that proof, Corollary 6.2 bounds the intermediate exceptional probability by $O(x^{-100})$. Conditional on its complement, the final application of Lemma 6.3 bounds the single-interval empty probability by $O(x^{-1-\varepsilon/2})$. Their sum gives (2). These statements concern the random residue classes themselves. [Banks, Ford and Tao, equations (1.7), (1.14) and proof of Theorem 7.1, pp. 33–34](https://arxiv.org/pdf/1908.08613)

Take $x=n^{A+4}$. Then $z\ge n$ for all sufficiently large $n$. Use the same forbidden residues at all primes up to $n$ in both sieves. Adding forbidden classes can only remove survivors, so $b_n(y+1)\ll x^{-1}$. Formula (1) now gives the exceptional probability $O(nx^{-1})$. Since $n(y+1)\le C_A B(n)$, this proves the tail bound.

Finally $f(n,m)\le n^2$ for every $m$. Each row has at least $n$ available multiples in $n^2$ consecutive integers, so one may choose its representative after at most $n-1$ earlier choices. Taking $A=3$ in the tail bound, the exceptional starts contribute $O(n^{-1})$ to the mean. This proves the theorem.

## A second proof of a fixed-power bound

The following argument proves the original existence of a fixed $\gamma$ using Mertens' estimates and bounded differences. It also permits conditioning the starting point on arbitrary congruences at small primes.

**Small primes.** There are absolute constants $C,c>0$ such that sieving $M\ge z^C$ consecutive sites by one arbitrary residue at each prime $p\le z$ always leaves at least $cM/\log z$ sites for sufficiently large $z$.

To see this, partition those primes into nonempty blocks
$\mathcal P_i=(z^{2^{-i-1}},z^{2^{-i}}]$, $i\ge0$. Mertens' reciprocal-prime estimate gives $\sum_{p\in\mathcal P_i}1/p\le D$ for an absolute $D$. Since $p\ge2$, each $V_i=\prod_{p\in\mathcal P_i}(1-1/p)$ is at least an absolute $v>0$. For a site let $I_i$ indicate avoidance of block $i$. Take $U_i$ to be its inclusion–exclusion expression stopped at even order $r_i=2(s+i)$, and $T_i$ the sum of all products of $r_i+1$ distinct hit indicators in this block. Bonferroni gives $0\le I_i\le U_i$ and $U_i-I_i\le T_i$. Telescoping the product gives
$$
 \prod_i I_i\ge W:=\prod_i U_i-\sum_i T_i\prod_{j\ne i}U_j .
$$
For independent uniform residues across primes, the block variables are independent, $\mathbb E U_i\ge V_i$, and $\mathbb E T_i\le D^{r_i+1}/(r_i+1)!$. Fix $s$ sufficiently large that the sum of these last bounds over $i\ge0$ is at most $v/2$. Factoring $\prod_i\mathbb E U_i$ out of $\mathbb E W$ now gives $\mathbb E W\ge\frac12\prod_i V_i$.

Every monomial in $W$ corresponds to a distinct squarefree modulus, since a correction exceeds the truncation in exactly one block. Its coefficient has absolute value one and its modulus is at most $z^J$, where $J=\sum_{i\ge0}(r_i+1)2^{-i}<\infty$. For fixed forbidden classes, the total of a monomial on $M$ sites differs from $M$ times its independent-residue expectation by at most one, by the Chinese remainder theorem. Hence the survivor count is at least $M\prod_iV_i/2-z^J$. Mertens' product estimate gives $\prod_iV_i\asymp1/\log z$, so $C=J+2$ suffices.

**Intermediate primes.** Take $z=(\log n)^2$ and $M=\lceil z^C\rceil$. Condition on all residue choices up to $z$ and let $X$ count the sites left after also sieving by $z<p\le M$. Each initial survivor remains with probability $\prod_{z<p\le M}(1-1/p)\asymp\log z/\log M$, hence $\mathbb E X\gg M/\log M$. Changing the class at one prime changes the count by at most $2\lceil M/p\rceil$. The sum of the squares of these bounds is $O(M^2/z)$. The bounded differences inequality therefore gives absolute constants $c_1,c_2>0$ with
$$
 \Pr\{X<c_1 M/\log M\}\le \exp(-c_2 z/(\log M)^2).
$$
This is $O_A(n^{-A})$ for each fixed $A>0$.

**Large primes.** Condition on the resulting set $S$ of sites. A prime $M<p\le n$ can hit at most one of them. Each site survives these primes with probability
$\theta=\prod_{M<p\le n}(1-1/p)\asymp\log M/\log n$.
For a fixed site $v$, condition on its surviving all of them. This conditional distribution can be obtained by resampling each prime whose original choice hits $v$, uniformly among the other classes. Every previously hit site other than $v$ stays hit. Thus if $E$ is the event that a prescribed collection of other sites is hit, $\Pr(E\mid v\text{ survives})\ge\Pr(E)$. Subtracting from $\Pr(E)$ gives $\Pr(E,\ v\text{ hit})\le(1-\theta)\Pr(E)$. Iteration bounds the probability that all of $S$ is hit by $(1-\theta)^{|S|}$. For $|S|\ge c_1M/\log M$ this is at most $\exp(-c_3 M/\log n)$ for some $c_3>0$.

These bounds show $b_n(M)\ll_A n^{-A}$ for every fixed $A>0$. Equation (1) and $f\le n^2$ give $\mathbb E f(n,m)\ll n(\log n)^{2C}$.

The same proof applies in any residue class $m\equiv a\bmod d$ when every prime factor of $d$ is at most $z$, with constants independent of $a,d$. Average over $dLP$. Conditional also on a feasible residue $r=m\bmod k$, write $m=kq+r$. The only constraint from $d$ on $q$ is one congruence modulo $d/\gcd(d,k)$. Because $dLP/k$ is divisible by $(d/\gcd(d,k))P$, the residues of $q$ at primes above $z$ remain independent and uniform, even after its residues at primes up to $z$ are fixed. The deterministic small-prime estimate is uniform in those fixed choices. Applying the row union bound gives the same superpolynomially small failure probability at interval length $nM$.

## A lower bound for comparison

Let $u=\lfloor n/2\rfloor$ and let $d_u$ be the natural density of integers with a divisor in $(u,2u]$. This set is periodic with period dividing $L$. A matching requires at least $u$ distinct sites of this kind, one for each of the $u$ indicated rows. Over a uniform starting residue, their expected number in $H$ sites is exactly $Hd_u$. Markov's inequality therefore gives
$$
 \Pr\{f(n,m)\le H\}\le Hd_u/u .
$$
Taking $H=\lfloor u/(2d_u)\rfloor$ gives $\mathbb E f(n,m)\gg u/d_u$. This is the lower-bound argument of Erdős and Pomerance, Theorem 5. Ford's estimate for the number of integers up to $x$ with a divisor in $(u,2u]$, applied as $x\to\infty$ with $u$ fixed, gives
$$
 d_u\asymp(\log u)^{-\delta}(\log_2 u)^{-3/2},
 \qquad \delta=1-\frac{1+\log\log 2}{\log 2}.
$$
Thus the mean is at least a constant times $n(\log n)^\delta(\log_2 n)^{3/2}$. Its precise order remains undetermined by these bounds. [Erdős and Pomerance, Theorem 5](https://math.dartmouth.edu/~carlp/PDF/matching.pdf) · [Ford, *The distribution of integers with a divisor in a given interval*, Ann. of Math. 168 (2008), 367–433](https://annals.math.princeton.edu/2008/168-2/p01)
