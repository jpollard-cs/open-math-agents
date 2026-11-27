# The least largest modulus at a prescribed cardinality

Codex, at the request of Jordan Pollard. Written proof for review, November 2026.

Let $m(k)$ denote the least possible largest modulus of an irreducible set of $k$ distinct covering moduli greater than one. In an irreducible set, every proper subset fails to cover the integers even when all its residues may be reassigned. For an integer $L$ put $f(L)=\sum_{p^a\parallel L}a(p-1)$. Let $m_{\mathrm{eq}}(k)$ denote the same minimum restricted to sets with $k=1+f(L)$, where $L$ is the LCM of their moduli. This is equality in the classical Znám–Simpson lower bound.

**Theorem.** Let $P_k$ be the $k$th prime. For each fixed $A>0$ and all sufficiently large integers $k$,
$$
 |m_{\mathrm{eq}}(k)-P_k|=O_A\!\left(\frac{k}{(\log k)^A}\right),
 \qquad
 m(k)\le P_k+O_A\!\left(\frac{k}{(\log k)^A}\right).
$$
In particular the unrestricted upper bound is $k(\log k+\log\log k-1+o(1))$. The original problem asks for the unrestricted minimum at each cardinality. The matching lower bound here applies to the stated equality class.

The [companion note](distribution.md) characterizes all possible weak limits of the normalized individual moduli when $X\sim k\log k$ and $f(L)\sim k$. The attainable extremal means are one quarter and three quarters of the largest modulus.

## A necessary prime-power bound

In an irredundant assignment choose a class whose modulus uses the full power $p^a\parallel L$, and a private residue $x$ for that class. All classes whose moduli divide $L/p$ miss $x$, hence miss all $p$ points $x+jL/p$, $0\le j<p$. Each remaining class has modulus divisible by $p^a$ and can cover at most one of those points because their residues modulo $p^a$ are distinct. At least $p$ distinct multiples of $p^a$ are therefore at most the largest modulus $X$, giving $p^{a+1}\le X$. This is the classical prime-power fiber argument.

In the equality class this gives the finite bound
$$
 k\le 1+\sum_{p^{j+1}\le X,\ j\ge1}(p-1)
   = \sum_{p\le\sqrt X}(p-1)+O(X^{2/3}\log X).
$$
For $j\ge2$, every summand has $p\le X^{1/3}$ and appears at most $\log_2 X$ times. For general irreducible covers the same fiber argument shows that all moduli are $\sqrt X$-smooth. Integers up to $X$ with a prime factor greater than $\sqrt X$ have a unique such factor, so Mertens' reciprocal-prime estimate gives $k\le(1-\log 2+o(1))X$. This last lower bound on $m(k)$ is a consequence of the known smoothness restriction.

## Hitting every cardinality

For a prime $q$ let
$$
 B(q)=1+f(\operatorname{lcm}(1,\ldots,q))
     =1+\sum_{p^j\le q,\ j\ge1}(p-1).
$$
Choose the first prime $q$ with $B(q)\ge k$, and let $r$ be the preceding prime. Write $D=B(q)-k$. Then $0\le D< B(q)-B(r)\le q+o(q)$. Indeed the only first-power increment is $q-1$. The squares in the entire range up to $q$ together contribute $O(q/\log q)$ by the prime number theorem, and powers of exponent at least three cost $O(q^{2/3}\log q)$.

Represent $D$ as a sum of $O(\log q)$ *distinct* weights $s-1$ over primes $s<q$. Take the largest admissible weight no greater than the current remainder. At an ordinary step with chosen prime $s$, Bertrand's postulate gives next prime at most $2s-1$, hence the new remainder is strictly less than $s-1$ and is at most half the old remainder up to an additive constant. If the first choice is capped by $s=r$ because $q$ is forbidden, $r\sim q$ and $D\le q+o(q)$ show that the new remainder is $o(q)$ and less than $r-1$. The final small steps work since weight 1 is available. This proves the claimed representation.

Start with $L_0=\operatorname{lcm}(1,\ldots,q)$, and for each chosen $s$ lower its exponent by exactly one. The resulting $L$ has $k=1+f(L)$, and the terminal prime $q$ occurs with exponent one. For each deleted digit the forbidden prime power $u_s=s^{\lfloor\log_s q\rfloor}$ is strictly larger than $\sqrt q$. This is immediate for $s>\sqrt q$, and otherwise follows from $s u_s>q$. Thus few small divisors have been lost. For $Y\le2q$, at most $YD_*/\sqrt q$ integers up to $Y$ are divisible by any of the deleted powers, where $D_*=O(\log q)$ is the number of removed digits.

## Assigning the residues and bounding their moduli

Process primes dividing $L$ in ascending order, and the base-$p$ digits at each prime from low to high. Let $W$ be the product of the fully processed prime powers of smaller primes. At digit $j$ of $p$, assign one distinct divisor $d$ of $W$ per nonzero digit $t$. The class has modulus $dp^j$, residue zero modulo $d$, and residue $tp^{j-1}$ modulo $p^j$. At the very last digit use $q$ distinct multipliers, assign all $q$ values including zero, and require the LCM of these multipliers to be $W$.

For $p\le\sqrt q$ take $d=1,\ldots,p-1$. All divide $W$, since none contain a deleted power and all their primes are smaller than $p$. Here $dp^j\le q^{3/2}$. For $p>\sqrt q$ we need only the first digit. We show that for each such $p$ there are at least $p$ divisors of $W$ at most
$$
 p+O\big(1+p\log q/\sqrt q\big).
$$
Take all numbers from 1 to $p-1$ and add the even numbers between $p$ and $p+H$, where $H=\lceil 20(1+pD_*/\sqrt q)\rceil$; for all sufficiently large $q$ one has $H<p$. Every candidate has all prime factors smaller than $p$. Each candidate up to $q$ divides $L_0$. Beyond $q$, a candidate failing to divide $L_0$ has a prime power greater than $q$ dividing it. As the candidate is even and smaller than $2q$, it must itself be a power of two. There is at most one such candidate. At most $(p+H)D_*/\sqrt q$ further candidates are excluded by deleted powers. The added even numbers supply at least $\lfloor H/2\rfloor$ candidates. Subtraction proves the claimed count.

At the terminal prime include each maximal prime power of $W$ as a multiplier. There are fewer than $q$ of them, all at most $q$. Fill the remaining slots with small divisors from the preceding paragraph. Their LCM is $W$. Every constructed modulus is at most
$$
 q^2+O(q^{3/2}\log q).
$$
The largest prime and its exponent distinguish different stages, and the multipliers distinguish the moduli within each stage.

Every integer is covered at its first nonzero digit, or at the final digit if all preceding digits are zero. All earlier coordinates vanish when that digit is reached, giving residue zero on its assigned multiplier. For arbitrary reassignment, consider any covering subset and thin it to an irredundant subsystem of LCM $E\mid L$. If $E<L$, at most $f(E)$ moduli in the whole construction divide $E$. Each of its eligible prime digits supplies at most $p-1$, with a potential extra only at the final digit. Having all $q$ final moduli available would force $E=L$ by their joint LCM. The Znám–Simpson inequality contradicts coverage at $E<L$. At $E=L$ it requires all $1+f(L)=k$ moduli. This proves irreducibility under reassignment.

## Inverting the estimates

Let $S(z)=\sum_{p\le z}(p-1)$. For every fixed $N>0$, the prime number theorem with logarithmic remainder and partial summation give
$$
 S(z)=\operatorname{li}(z^2)+O_N(z^2/\log^N z).
$$
Indeed the main term for $\sum p$ is $\int_2^z t\,dt/\log t=\operatorname{li}(z^2)+O(1)$, and subtracting $\pi(z)$ is absorbed by the stated error. Higher prime powers in $B(q)$ cost $O(q\log q)$ by summing over bases up to $\sqrt q$. The size construction yields $k=S(q)+O(q\log q)$, hence $q^2\sim k\log k$. Both $\operatorname{li}(q^2)$ and $\operatorname{li}(P_k)$ differ from $k$ by $O_N(k\log k/(\log k)^N)$. The mean value theorem and $P_k\sim k\log k$ give $q^2=P_k+O_A(k/(\log k)^A)$ after choosing $N>A+2$. The construction error $O(q^{3/2}\log q)$ is absorbed as well.

For the reverse inequality, put $X=m_{\mathrm{eq}}(k)$, which exists for every sufficiently large $k$ by the construction. We have $k\le\operatorname{li}(X)+O_N(X/\log^N X)$ by the necessary bound. Also $k<X\ll k\log k$. If $X<P_k$, subtract this lower estimate on $\operatorname{li}(X)$ from the PNT estimate on $\operatorname{li}(P_k)$ and use the mean value theorem as before. This proves the claimed two-sided bound for $m_{\mathrm{eq}}(k)$. Finally $P_k=k(\log k+\log\log k-1+o(1))$ by inversion of the PNT.

## Verification, antecedents and scope

The accompanying Python program takes an exact $k$ and outputs the list of moduli and residues. The default run checks sizes 5 through 1,000 with a second routine that recovers the prime digits from the actual congruences. It exhaustively checks covering, private points, and the divisor budget when the period is at most 200,000. The small-$k$ fallback uses the powers-of-two construction and is irrelevant to the asymptotic. The Lean file imports the actual Formal Conjectures definition of an irreducible covering set. It proves that whenever a member is divisible by a positive power of a prime, the largest modulus is at least the next power, with no period data required from the caller. Lean 4.33.1 reports only the standard axioms of propositional extensionality, choice and quotient soundness. The asymptotic and distribution theorems have written proofs. Its historical priority and independent review remain open.

At $k=100{,}000$ the two choices of cofactors each produce exactly 100,000 distinct moduli with maximum 1,332,868. Direct inspection of each modulus and assigned residue gives normalized means 0.242136 and 0.719413. Across sizes 5 through 1,000 the full-period check applied at 37 sizes for each choice.

The initial plan to use all digits through a cutoff without adjustments missed most sizes. Deleting a logarithmic number of top digits fills each gap while keeping the small-divisor estimate. The argument for the lower bound uses equality in $k\ge1+f(L)$. Arbitrarily many classes above that lower bound remain possible in principle. To improve the unrestricted lower bound one must control those sets, or construct examples from them to lower the upper bound.

- [Erdős, 1980 survey, printed p. 95](https://www.renyi.hu/~p_erdos/1980-03.pdf).
- [The question and its four original quantifiers](https://www.erdosproblems.com/latex/1189)
- [Paratelligent Research Agent and Jeff Pickhardt, *Irreducible Covering Sets*](https://paratelligent.com/research/papers/irreducible-covering-sets-a-solution-of-erds-problem-1189-N4zQ0x6W). Their work already gives the exponent $1+o(1)$ with exact-cardinality digit frames. The July claim is recorded with a $Ck(\log k)^2$ bound.
- [Colin Snyder, Star Fleet Math, Problem 1189](https://www.starfleetmath.com/). Its formalized bound has six logarithmic factors.
- [Zhi-Wei Sun, *On covering numbers*](https://arxiv.org/abs/math/0601017), for the digit construction and prime-power multiplicity antecedents.
- [Balister, Bollobás, Morris, Sahasrabudhe and Tiba, *The structure and number of Erdős covering systems*](https://arxiv.org/abs/1904.04806), for the classical period bound.
- [Pedro Martins, preprint on Problem 1188](https://doi.org/10.5281/zenodo.23427851), for related small-modulus constructions for minimal assignments, a different irreducibility condition.
- [Giuseppe Molteni, analytic number theory notes, Theorem 1.4](https://sites.unimi.it/molteni/didattica/matematica/analytic_number_theory/appunti-AnNTh.pdf), for the prime number theorem with logarithmic remainder.
