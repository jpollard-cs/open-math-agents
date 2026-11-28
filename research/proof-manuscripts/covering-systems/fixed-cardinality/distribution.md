# Where the moduli of near-optimal covers can lie

This companion to [the exact-cardinality construction](README.md) is an AI-authored written proof. It describes a constraint on every cover in the stated regime, and gives two sequences of covers attaining it.

Let $M$ be an irreducible covering set of $k$ distinct moduli, $X=\max M$, and $L=\operatorname{lcm}(M)$. Consider any sequence with $k\to\infty$, $X\sim k\log k$ and $f(L)\sim k$. In particular these hypotheses hold for asymptotic minimizers under $k=1+f(L)$. Write $F_M(t)=k^{-1}\#\{n\in M:n\le tX\}$.

**Theorem.** For $0<t<1$,
$$
  t+(1-t)\log(1-t)\ \le\ \liminf F_M(t)
   \ \le\ \limsup F_M(t)\ \le\ t(1-\log t).
$$
Both envelope functions are sharp *simultaneously for all* $t$. Each is attained as the limit of a construction available at every sufficiently large exact cardinality $k$. Consequently the sharp limiting bounds on the mean modulus divided by the largest are $1/4$ and $3/4$.

### A lower bound for occupancy in an arbitrary interval

Set $z=\sqrt X$. Higher prime powers in $f(L)$ account for $O(X^{2/3}\log X)=o(k)$, by the prime-power cap in the main paper. Also $\sum_{p\le z}(p-1)\sim X/\log X\sim k$. It follows from $f(L)\sim k$ that the sum of $p-1$ over all missing primes $p\le z$, $p\nmid L$, is $o(k)$.

Take an interval $J$ in $[0,X]$ of length $sX$ with $0<s<1$ fixed. Every prime $p\mid L$ with $p>\sqrt s\,z$ supplies at least $p$ distinct moduli divisible by $p$. At most $sX/p+1$ multiples of $p$ can lie in $J$. Counting moduli outside $J$ across these primes thus gives at least the sum of $p-sX/p-1$. Omitting the missing primes changes the sum by $o(k)$, since each positive summand is at most $p$. Replacing the count with a union also costs $o(k)$. Indeed two primes in the chosen range have at most $1/s$ common multiples up to $X$, and there are $O_s((z/\log z)^2)$ pairs. This bounds the total overcount even if a modulus is counted three or more times.

PNT and partial summation on the fixed interval $[\sqrt s,1]$ give
$$
 \frac1k\sum_{\sqrt s\,z<p\le z}\big(p-sX/p-1\big)
       \longrightarrow 2\int_{\sqrt s}^1(y-s/y)\,dy=1-s+s\log s .
$$
Taking $J=[0,tX]$ proves the upper envelope. Taking $J=(tX,X]$ gives the lower envelope.

### Witnesses for both extremes

In the construction of the main paper write $q$ for the final prime. Its maximum $X$ satisfies $X/q^2\to1$ by the upper bound and the necessary estimate for the equality class. Fix $\epsilon>0$. Stages with primes $p<\epsilon q$ contribute at most $(\epsilon^2+o_\epsilon(1))k$ classes by PNT, including the negligible cost of higher powers. The lone terminal stage has $o(k)$ classes. Among the other primes $\epsilon q\le p<q$ at most $O(\log q)$ were deleted. Every remaining stage contributes $p-1$ moduli $pd$.

Uniformly for $\epsilon q\le p<q$, all but $o_\epsilon(q)$ of the integers up to $2q/\epsilon$ divide the earlier prime-power product $W$. To see this, remove multiples of primes at least $p$, of which there are $O_\epsilon(q/\log q)$ by PNT since each such prime has $O_\epsilon(1)$ multiples. The deleted prime powers remove $O_\epsilon(\sqrt q\log q)$ integers. A prime power of exponent at least two above $q$ can exclude only $O_\epsilon(\sqrt q\log q)$ integers as well, by counting all such prime powers up to $2q/\epsilon$ and their bounded number of multiples. These exhaust the reasons for failing divisibility.

For the first witness take the $p-1$ smallest divisors, as in the main proof. Relative to the integer interval $[1,p]$ this changes $o_\epsilon(q)$ cofactors per prime in symmetric difference. For the second witness at the same stage put
$$
 T_p=\max\big(\lfloor q^2/p\rfloor,\ \text{the }(p-1)\text{st smallest divisor of }W\big)
$$
and take the $p-1$ largest divisors up to $T_p$. The small-divisor bound gives $T_p=q^2/p+o(q)$ on this range. The selected cofactors differ in $o_\epsilon(q)$ places from the integers in $[q^2/p-p,q^2/p]$. At every nonterminal stage with $p>\sqrt q$ this rule keeps $p T_p\le q^2+O(q^{3/2}\log q)$ by the main proof. Smaller and terminal stages keep their original choices. The assignment and the irreducibility proof apply to either choice.

The total symmetric differences over bulk primes are $o_\epsilon(k)$. With cutoff $tq^2$, counting the first ideal intervals and dividing by $k$ gives, as $\epsilon\downarrow0$,
$$
  2\int_0^1\min(y,t/y)\,dy=t(1-\log t).
$$
The second ideal intervals reflect the products of the first about $q^2/2$, up to integer endpoint rounding, so their limit is $1-(1-t)(1-\log(1-t))$. Continuity and $X/q^2\to1$ allow $tX$ in place of $tq^2$. These proofs apply to every fixed $t$ for the same two sequences. Integrating the tail bounds by Fatou's lemma (and the reverse inequality for uniformly bounded functions) gives the stated bounds on mean, attained by each witness. Equivalently, the two limiting distributions are those of $UV$ and $1-UV$ for independent uniform variables $U,V$ on $[0,1]$.

A sequence improving the unrestricted largest-modulus upper bound by a constant factor must leave this regime. More precisely, $X\le(c+o(1))k\log k$ for fixed $0<c<1$ forces $k-1-f(L)\ge(1-c-o(1))k$ by the universal cap on $f(L)$ and $X>k$. Constructing such sets with irreversible dependence on every modulus after arbitrary reassignment remains an open direction.

### All attainable limiting distributions

In fact there is a complete description. Write $G(s)=s(1-\log s)$ for $0<s\le1$, and $G(0)=0$. A Borel probability measure $\mu$ on $[0,1]$ is a weak limit for covers in the regime above **if and only if** for every Borel set $E$,
$$
                       \mu(E)\le G(|E|),
$$
where $|E|$ is Lebesgue measure. Every such law is attained with $k=1+f(L)$, $X\sim k\log k$, and with a cover constructed at every sufficiently large exact size $k$. In particular these measures are absolutely continuous.

For necessity the interval counting argument applies to any fixed union of $r$ intervals of total length $s$ in normalized coordinates. The bound on multiples of $p$ in the union becomes $sX/p+O(r)$, whose total extra error is $O_r(\pi(z))=o(k)$. Thus the proportion of moduli in the union is at most $G(s)+o(1)$. Under weak convergence the bound passes to finite relatively open unions by the open-set inequality. Every relatively open set is an increasing union of such finite unions. Outer regularity of Lebesgue measure and continuity of $G$ extend the estimate to every Borel set.

For sufficiency fix a partition into $h$ equal cells (half-open, including 1 in the last cell). Set $v_i=\mu(I_i)$ and $w_i=G(i/h)-G((i-1)/h)$. The $w_i$ decrease. For each set of $j$ cells the sum of its $v_i$ is at most $G(j/h)$, the sum of the first $j$ values of $w$. Thus $v$ lies in the convex hull of the permutations of $w$. For completeness, take any linear functional, order its coefficients in decreasing order and write it as a sum of nonnegative multiples of prefix sums plus a constant times the full sum. The inequalities just proved show its value on $v$ is at most its maximum over the permutations of $w$. Finite-dimensional separation gives the assertion. Fix a convex combination representing $v$.

Each permutation of cells can be realized by translating the normalized cofactor products separately within those cells. More precisely, work at scale $q^2$. For a prime $p$ in a fixed bulk range $\epsilon q\le p<q$, the unpermuted ideal products occupy $[0,p^2/q^2]$ at spacing $p/q^2$. Let $T$ translate each partition cell to its chosen image. Select the allowed integer cofactors $d$ for which $pd/q^2$ belongs to $T([0,p^2/q^2])$. This set is a union of at most $h$ intervals with total length $p^2/q^2$. Before the divisibility check there are $p+O(h)$ positive integer cofactors in these intervals. The number in each cell differs by $O(h)$ from the ideal count in its inverse image cell. After restriction to $d\mid W$, at most $o_\epsilon(q)$ more are lost, uniformly in the prime and the permutation, by the preceding small-divisor estimate. Trim to $p-1$ divisors or fill the shortfall from the smallest available divisors. Each row then has two properties: its cell counts differ by $o_{h,\epsilon}(q)$ from the permuted ideal counts, and its largest modulus is at most $q^2+O(q^{3/2}\log q)$. For definiteness this same selection rule can be used at every nonterminal $p>\sqrt q$, since the fill uses the original small divisors. In the estimates simply bound the mass of all primes $p<\epsilon q$ by $O(\epsilon^2)+o(1)$. Keep the smaller and terminal digits of the main construction as before. Its proof of irreducibility is unchanged.

Independently at each eligible prime choose the permutation with the probabilities in the convex combination. By the bulk estimates, PNT and then $\epsilon\downarrow0$, the expected vector of normalized cell counts tends to $v$ as $k\to\infty$. Each coordinate has variance at most $\sum_{p\le q}p^2/k^2=O(q/k)=o(1)$, since at most $p$ counts at one prime share a random choice and $\sum_{p\le q}p=O(k)$. The sum of the squared deviations of the cell masses from their expectations therefore has expectation $o_h(1)$. Some deterministic choices achieve at most that expectation. The choices can be made explicitly. Keep the cumulative vector of counts minus expected counts. At each prime, choose the permutation minimizing the squared norm of the updated vector. Its weighted average over the available permutations is the old squared norm plus the sum of the coordinate variances at that prime. The minimizing choice obeys the same final variance bound. The companion program `permutations.py` implements this rule with integer arithmetic for rational mixture weights, including a separate overflow cell. This establishes approximation at every sufficiently large size for the fixed partition. Counts here use scale $q^2$; the possible fraction above 1 tends to zero, since the trimmed or filled bulk rows change only $o_{h,\epsilon}(q)$ slots each, and the low and terminal stages have arbitrarily small limiting mass.

Finally use dyadic partitions with mesh tending to zero. For each fixed partition choose a size threshold beyond which the sum of absolute cell errors and the overflow are at most its mesh; make these thresholds strictly increasing and unbounded. At each $k$ use the finest partition whose threshold has been reached. Uniform continuity of continuous test functions on a fixed compact interval proves weak convergence to $\mu$. Normalizing by the actual $X$ in place of $q^2$ preserves the limit because $X/q^2\to1$. This proves sufficiency. The construction gives the uniform law, rearrangements of the density $-\log t$, and all densities satisfying the displayed concentration condition.
