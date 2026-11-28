# A quantitative refinement of the lower bound for the factorial doubling time

Jordan Pollard · November 27, 2026  
OpenAI Codex developed the argument and prepared this note.

Let $D(n)=\tau(n!)$, $G(n,H)=\log(D(n+H)/D(n))$, and let $K(n)$ be the least positive integer $h$ for which $D(n+h)\ge2D(n)$. Write $\log_j$ for the $j$-fold iterated logarithm. Define
$$
R(v)=\frac{v\log v\,\log_3 v}{(\log_2 v)^2},\qquad
A_0=\sum_{s=1}^{\infty}\frac{\log(1+1/s)}s=1.2577468869\ldots .
$$
Freiberg proved $\limsup K(n)/R(\log n)\ge 3/(4\pi^2)$ by allowing a small number of offsets to remain uncovered in a construction of Erdős, Graham, Ivić and Pomerance. His proof also counts a positive fraction of lifts in its selected class. We retain his covering, vary the number of lifts, and estimate the logarithmic change in the divisor count directly. The constant $A_0$ already occurs in the 1996 paper. [Freiberg, *Long runs of integers with small prime factors and the divisor function of n!*, Theorem 1.1 and Section 5](https://arxiv.org/abs/2609.15597) · [Erdős, Graham, Ivić and Pomerance, *On the number of divisors of n!*](https://math.dartmouth.edu/~carlp/factorial.pdf)

**Theorem.** For every fixed $0<c<\log 2/(2A_0)=0.2755511414\ldots$ and all sufficiently large $Y$, every interval $[X,X+Y]$ with integer $X\ge Y$ contains at least $Y^{1-o(1)}$ integers $n$ for which $G(n,\lfloor cR(\log Y)\rfloor)<\log 2$. The error in the count is uniform in $X$. In the interval $[Y,2Y]$ one may take any $0<c<\log 2/A_0=0.5511022828\ldots$. Consequently
$$
\limsup_{n\to\infty}\frac{K(n)}{R(\log n)}\ge\frac{\log 2}{A_0}.
$$
Here $R(\log n)$ is the same scale as in Freiberg's theorem. These constant refinements do not decide Erdős 420(i), which asks for divergence on every sufficiently large start at a fixed power of $\log n$.

## Counting uncovered offsets

Write $L=\log Y$, $u=L/\log_3Y$, $w=\log u$, $w_2=\log w$, $w_3=\log w_2$ and $H=\lfloor cR(L)\rfloor$. Then
$$
\log H\sim w,\qquad \log(H/u)\sim w_2,\qquad
H=(c+o(1))Lww_3/w_2^2.
$$
Fix $0<e<1/2$ and take $z=u^{(1-e)w_3/w_2}$. The modulus $M_0$ is the product of primes in $[w^2,u]$. For the translated result take $M=M_0$. For the dyadic result, we will allow the removal of a single prime $r\mid M_0$ before arranging the covering. In both cases
$$
B:=M/\varphi(M)=(1+o(1))w/(2w_2),\qquad M=\exp((1+o(1))u)=Y^{o(1)}.
$$

Prescribe $A\equiv0\pmod p$ for the primes $z<p\le u$ dividing $M$. With all primes available, every surviving $i\le H$ is $z$-smooth or is divisible by a prime greater than $u$. The latter number is at most $\sum_{m\le H/u}\pi(H/m)\le(1+o(1))Hw_2/w$ by the prime number theorem and $\log(H/u)\sim w_2$. The smooth-number estimate used in Freiberg's (5.8)–(5.10) applies with this $H$. Specifically $v=\log H/\log z\sim w_2/((1-e)w_3)$, so $v\log v\sim w_2/(1-e)$, $v\log_2 v=o(w_2)$ and $v<\log z$. The uniform de Bruijn estimate there gives $\Psi(H,z)/H\le w^{-1/(1-e)+o(1)}$. This uses the displayed asymptotics for $H$, and places no restriction on a fixed multiplier $c$. Omitting a prime $r>z$ adds at most $H/r+1=o(Hw_2/w)$ survivors. Hence initially at most $(1+o(1))Hw_2/w$ offsets survive.

For the remaining primes $w^2\le p\le z$ dividing $M$, prescribe a residue for $-A$ that covers as many survivors as possible. Each leaves at most a fraction $1-1/p$. The product of these fractions is $(1+o(1))2w_2/\log z$ by Mertens' theorem. Omitting a single prime from this product changes it by at most $(1-1/w^2)^{-1}$. Choose $A$ by the Chinese remainder theorem and set $T=\{1\le i\le H:(A+i,M)=1\}$. This proves the version of Freiberg's (5.11) needed here:
$$
|T|\le\left(\frac{2}{1-e}+o(1)\right)\frac{H w_2^3}{w^2w_3}. \tag{1}
$$

## Estimating the gain for translates

Average over $n\in[X,X+Y]$ with $n\equiv A\pmod M$. Their number is $J+O(1)$ with $J=Y/M$ and $\log J\sim L$. Put $Q=\lfloor u^3\rfloor$ and $a_s=\log(1+1/s)$. The contributions from primes $p\le\sqrt{n+i}$ sum to at most $2H/\sqrt Y$. Indeed a single prime's contribution at $m=n+i$ is at most $v_p(m)p/m$, and summation using $p/\log p\le\sqrt m/\log\sqrt m$ gives the bound. A prime above $\sqrt m$ contributes exactly $a_s$ if $m=sp$, since $s<p$ and $v_p((m-1)!)=s-1$. Terms with $s>Q$ cost at most $H/Q$. Both errors tend to zero uniformly.

For offsets outside $T$, a prime factor of $M$ divides $n+i$. A representation $n+i=sp$ with $s\le Q$ therefore has $s\ge w^2$, because $p\ge Y/Q>u$. For each $s$, put $g=(s,M)$. At most $H/g+1$ offsets permit the divisibility $s\mid n+i$. At each such offset the possible $p$ lie in one residue class modulo $M/g$ in an interval of length $Y/s$ (enlarging by two handles endpoints). A noncoprime class contains no eligible prime because $p>u$. The modulus divides $M$, and $\log((Y/s)/(M/g))\sim L$ uniformly for $s\le Q$. Short-interval Brun–Titchmarsh gives $\ll JB(H+g)/(s L)$ pairs after summing offsets. Since $a_s\le1/s$, the average over lifts of the covered contribution is
$$
\ll\frac{B}{L}\left(\frac{H}{w^2}+B\right)=o(1).
$$
Here $\sum_{s\ge w^2}s^{-2}\ll w^{-2}$ and $\sum_s(s,M)/s^2=\zeta(2)\sum_{d\mid M}\varphi(d)/d^2\ll B$. The first term in the bound is $O(w_3/w_2^3)$. [Short-interval Brun–Titchmarsh inequality, Lemma A.4](https://ems.press/content/serial-article-files/39116)

At a fixed $i\in T$, all eligible $s$ are coprime to $M$. The possible primes occupy one reduced residue class modulo $M$ in an interval of length $Y/s$. Brun–Titchmarsh with its constant $2$ bounds their number by $(2+o(1))JB/(sL)$ uniformly for $s\le Q$. Weighted by $a_s$ and summed, the mean contribution per uncovered offset is at most $(2+o(1))B A_0/L$. Using (1) and $H\sim cLww_3/w_2^2$, we obtain
$$
\mathbb E\, G(n,H)\le \frac{2c A_0}{1-e}+o(1).
$$
Choose $e$ so the right side has limit superior less than $\log2$. A fixed positive fraction of the $Y^{1-o(1)}$ lifts then has gain strictly below $\log 2$ by Markov's inequality. This proves the translated assertion.

## An improved coefficient on dyadic intervals

When $X=Y$, we can count the primes for each uncovered offset with coefficient $1$ in place of $2$. We give the details of exceptional characters because the modulus $M$ exceeds every fixed power of $\log Y$.

Consider the possible exceptional zero associated with modulus $M_0$. The classical zero-free region for the product over all Dirichlet characters modulo $M_0$ permits at most one zero with real part $>1-c_1/\log M_0$ and $|\operatorname{Im}s|\le1$, for an absolute $c_1>0$. It is real and belongs to a nonprincipal real character. If it exists, remove one prime $r$ dividing the conductor of its primitive character, setting $M=M_0/r$. The modulus $M_0$ is squarefree, so this conductor cannot divide $M$. If there is no such zero, retain $M=M_0$. Every character modulo $M$ induces a character modulo $M_0$; the extra Euler factors can have no zero near $1$. Consequently any exceptional zero $\beta$ in a prime number theorem for modulus $M$ satisfies $1-\beta\ge c_1/\log M_0$. These facts also follow from the zero-free region and exceptional-zero definition in Section 1 of Thorner and Zaman. [Thorner and Zaman, *Refinements to the prime number theorem for arithmetic progressions*, equations (1.1)–(1.2)](https://arxiv.org/pdf/2108.10878)

For $x\asymp Y/s$ and $s\le Q$, we have $x\ge M^{12}$ and $\log x/\log M_0\to\infty$ uniformly. Corollary 1.4 and Remark 1.5 of Thorner and Zaman give, uniformly in every reduced class $v\pmod M$,
$$
\sum_{p\le x,\ p\equiv v\,({\rm mod}\ M)}\log p
=\frac{x}{\varphi(M)}(1+o(1)).
$$
Indeed the two error terms in their corollary tend to zero uniformly, and a remaining exceptional correction is $O(x^{\beta-1}/\beta)=o(1)$ by the preceding construction. For an uncovered offset take the difference at $(Y+i)/s$ and $(2Y+i)/s$. These endpoints are comparable to their difference, so the weighted count is $(1+o(1))Y/(s\varphi(M))$. Integer endpoints cost at most one prime; $J/Q\to\infty$ faster than any power of $\log Y$. Dividing by $(1+o(1))\log Y$, the common logarithmic size of all these primes, gives at most $(1+o(1))JB/(sL)$ primes. [Prime number theorem used here, Corollary 1.4 and Remark 1.5](https://arxiv.org/pdf/2108.10878)

The covering estimate (1) included the effect of omitting one prime. The covered offsets still cost $o(1)$ by Brun–Titchmarsh. Thus in the dyadic interval the mean is at most $c A_0/(1-e)+o(1)$. Taking $c<\log2/A_0$ proves the stronger assertion. Passing from $R(\log Y)$ to $R(\log n)$ for $Y\le n\le2Y$ costs a factor $1+o(1)$.

## Windows below this scale

If $h(Y)$ is a positive integer with $h=o(R(\log Y))$, every interval $[X,X+Y]$, $X\ge Y$, contains $Y^{1-o(1)}$ starts $m$ with $G(m,h)=O(h/R(\log Y))=o(1)$. Apply the translated result in $[X,X+\lfloor Y/2\rfloor]$ at a fixed admissible $c$. In each good $H$-window take $\lfloor H/h\rfloor$ successive $h$-windows. Their log gains sum to at most $\log2$, so one has gain at most $\log2/\lfloor H/h\rfloor$. The selected $m$ stay in the original interval. Different original lifts differ by at least $M>H$, so give different $m$.
