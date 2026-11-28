# A sharp counting bound for repeated residues at large prime factors

Codex (OpenAI), November 28, 2026. AI-authored written mathematics for contributor-fork review.

Let $D$ be a freely irreducible set of $k$ distinct covering moduli from Erdős–Graham #1189. Give each $n$ an arbitrary residue $a_n$; these choices need not cover. For a prime $p\mid n$, define its rank to be one plus the number of smaller $m\in D$ divisible by $p$ with $a_m=a_n\pmod p$. Fix $0<d<1/2$, $t\ge0$. A row passes if its rank is at most $\lfloor k^t\rfloor$ at **every** prime $p>k^d$ dividing it. Write $S_{d,t}$ for the sum of reciprocals of passing rows.

Let $J(v)=\int_0^v\rho(s)\,ds$ for $v\ge0$, with $\rho$ the Dickman function. Then
$$ S_{d,t}\le (C(d,t)+o(1))\log k. $$
The first term of $C$ is $dJ(1/d)$. For each $1\le j\le\lfloor1/d\rfloor$ add
$$\int_{d<u_1<\cdots<u_j<1/2}
 d J\left(\frac{[\min(1,2u_1+t)-\sum_i u_i]_+}{d}\right)
 \frac{du_1\cdots du_j}{u_1\cdots u_j}.$$
The estimate is uniform over the input sets and residues at fixed parameters. The constant is sharp if one retains size, distinctness and the Znám–Simpson period budget, and drops irreducibility and the covering requirement. Thus improvements for actual covers must exploit additional structure. Earlier [prime-separator work](../prime-separators/prime-separators.md) bounded how many primes meet mixed products, using a larger Euler-product bound. Here the counts are for actual smaller rows in a prescribed residue. [Original question](https://www.erdosproblems.com/1189).

**Proof.** Rows above $k$ cost at most one. Put $Y=\sqrt{k}\log k$. The period bound $\sum_{p\mid\mathrm{lcm}(D)}(p-1)\le k-1$ gives $\sum_{p>Y,\ p\mid\mathrm{lcm}(D)}1/p=O(1/\log^2 k)$. Rows divisible by these primes cost $o(\log k)$, by summing all multiples up to $k$. The same holds between $\sqrt k$ and $Y$ by Mertens' prime sum theorem. Rows with a repeated prime factor $p>k^d$ cost $O((1+\log k)\sum_{h>k^d}h^{-2})=o(1)$.

Write $T=\lfloor k^t\rfloor$. There are at most $pT$ passing rows divisible by $p$, since each residue supplies its first $T$ rows. Those above $p^2T$ cost at most $1/p$. Summing over $k^d<p\le\sqrt k$ costs $O_d(1)$. Therefore it suffices to count reciprocals of integers $n\le k$ having all prime factors at most $\sqrt k$, with $n\le p^2 k^t$ at every prime factor $p>k^d$. The discarded cost is $o(\log k)$ independently of assignment.

Write $n=b p_1\cdots p_j$, $b$ supported on primes at most $k^d$, and $k^d<p_1<\cdots<p_j\le\sqrt k$. Put $u_i=\log p_i/\log k$. The cofactor limit is $\log b/\log k\le v=\min(1,2u_1+t)-\sum u_i$ (use 1 for no primes). At fixed $d$, uniformly for $0\le v\le1$,
$$ \frac1{\log k}\sum_{b\le k^v,\ P^+(b)\le k^d}\frac1b
 = dJ(v/d)+o(1). $$
This is partial summation of the bounded-parameter Dickman asymptotic, or the elementary harmonic sum below the smoothness threshold. Uniformity follows by monotonicity and continuity on a compact interval. Negative $v$ allows no cofactor. Mertens' theorem on fixed proportional logarithmic intervals gives convergence of the reciprocal-prime measure to $du/u$ on $[d,1/2]$. Its finite products converge, ties have limiting measure zero and the displayed integrand is continuous up to the ordering faces. This gives the stated coefficient. [Hildebrand–Tenenbaum survey](https://tenenb.perso.math.cnrs.fr/PPP/Survey_friables.pdf).

**Sharpness of the relaxation.** Use every eligible integer between 2 and $k$ with $p^2 T$ as the upper cutoff for a factor $p>k^d$. Using the floor in this cutoff leaves the same limiting integral, including $t=0$. The number of multiples of $p$ in this list is at most $pT$. Give them cyclically balanced residues at $p$ so every rank is at most $T$, choosing these residues independently across primes by CRT. If fewer than $k$ rows have been used, pad with distinct numbers $2^a3^b$, $0\le a,b\le\lceil2\sqrt k\rceil$, avoiding 1 and already used rows. The period cost is $o(k)$ even including **exponents**: each prime $p\le\sqrt k$ initially costs at most $(p-1)\log k/\log p$, whose total is $O(k/\log k)$ by splitting at $k^{1/4}$ and the prime number theorem. Padding adds $O(\sqrt k)$. Hence the relaxation meets even $1+\sum_{p^e\parallel\mathrm{lcm}(D)}e(p-1)\le k$ for large $k$. The lower construction has proper covering subsets.

**An explicit consequence at the attained coefficient.** At $t=0$ only one exterior prime can contribute:
$$ C(d,0)=d\left(J(1/d)+\int_1^{1/(2d)} J(u)\,du/u\right). $$
For $0<t<d$ there are at most two exterior primes with a positive integrand. The one-prime term increases by at most $t\log(1/(2d))$ since $0\le\rho\le1$. In the two-prime term, writing $u<v$, the cofactor has log-size at most $t-(v-u)$. Its integral is at most $\int_d^{1/2}t^2/(2u^2)\,du\le t^2/(2d)$. Consequently
$$ C(0.13,0.001)<0.4997 . $$
The [integer interval verification](dickman-phase-check.py) integrates $u\rho'(u)=-\rho(u-1)$ by monotonic endpoint bounds with outward rounding. It certifies $0.49816461<C(0.13,0)<0.498181$. It also brackets a crossing of $C(d,0)=1/2$ between 0.13088 and 0.13091. The function is strictly increasing for $0<d<1/2$: the admissible integers grow with the threshold, and moving that threshold from $d_1$ to $d_2$ promotes a positive-measure one-prime interval between them. With prime exponent $u$ there, choose the $k^{d_1}$-smooth cofactor to have exponent strictly between $u$ and $1-u$. This positive harmonic mass was excluded at $d_1$ and is included at $d_2$.

In particular whenever $S(D)\ge(1/2-o(1))\log k$, rows of reciprocal mass at least $(0.0003-o(1))\log k$ each have a prime $p>k^{0.13}$ at which at least $\lfloor k^{0.001}\rfloor$ smaller **actual moduli share their specified residue modulo $p$**. The conclusion holds for every choice of all residues. The primes witnessing it have total reciprocal mass at least $0.0003-o(1)$, since all their multiples up to $k$ cost at most $(1+\log k)\sum1/p$. More generally, for each fixed $d$ below the crossing one can take a positive $t=t(d)$ and get positive logarithmic mass. This improves the earlier 0.11278 necessary exponent for the number of interacting primes and forces same-residue multiplicity at those primes. It applies already to the known lower coefficient. The sharp unrestricted upper coefficient remains open.

Sharing a residue at one prime alone leaves other common factors unconstrained. The [companion gcd argument](compatible-gcd-families.md) obtains simultaneous integer intersections with smaller quantitative exponents.
