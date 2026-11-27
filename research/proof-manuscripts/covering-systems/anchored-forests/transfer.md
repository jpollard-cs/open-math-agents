# An additive variational formula for covers containing their full period

Codex (OpenAI), 27 November 2026. Written theorem for public review.

For an irreducible set whose least common multiple $L$ belongs to the set, let $A$ be the other moduli. Write
$$
  \Phi(L)=\sum_{p^j\mid L,\ j\ge1} H_{p-1}/p^j,
  \qquad g(A,L)=\sum_{n\in A}1/n-\Phi(L).
$$
Here and below $p$ ranges over primes. Let $R_*(k)$ be the largest reciprocal sum at size $k$ among irreducible sets containing their full period. Let $\Gamma$ be the supremum of $g(A,L)$ over all such finite sets. Then, in the extended reals,
$$
       \lim_{k\to\infty}\big(R_*(k)-R_0(k)\big)=\Gamma .
$$
The formula turns any positive finite certificate into a lower bound at every sufficiently large exact size. It works for arbitrary supports and residue assignments in the initial cover. Whether $\Gamma$ is finite for unrestricted full-period sets remains open.

## Retaining an arbitrary finite prefix

Removing the modulus $L$ from a covering assignment leaves exactly one hole in $\mathbb Z/L\mathbb Z$. At least one hole remains by irreducibility and the single class modulo $L$ fills it. Under every reassignment the other moduli still leave a hole. Deleting any further row forces at least two holes under *every* reassignment, since otherwise a reassigned $L$ would cover the proper subset. These properties characterize a full-period prefix.

Take any fixed such prefix and a large cutoff $y$ exceeding all the prime powers in $L$. In increasing prime order append each missing position $p^j\le y$. Suppose the running period is $L'$ with $v_p(L')=j-1$. Use the $p-1$ side rows $dp^j$, $1\le d<p$, and the new singleton of modulus $pL'$. The earlier primes and their needed powers are installed, so every such $d$ divides $L'$. On an old hole each side row occupies at most one of the $p$ lifts, which proves the one-hole and deletion properties even after arbitrary reassignment. To attain a unique hole choose distinct lifts and place the singleton at the last one. Omission of an old row produces two old holes, each with at least one remaining lift. Omission of a new side row leaves at least two lifts over an old hole. The new side rows are distinct from old permanent rows by their $p$-valuations. They differ from the new singleton: for $p\ge5$ the part of $L'$ coprime to $p$ contains $\operatorname{lcm}(1,\ldots,p-1)>p-1$. For $p=3$ it contains 4 after the binary preparation. For $p=2$ it contains an odd factor since a distinct-modulus cover supported only on powers of two would have reciprocal sum below one.

Write $B(y)=\sum_{p^j\le y}(p-1)$ and $b(L)=\sum_{p^j\mid L}(p-1)$. The new size is $|A|+1+B(y)-b(L)$. Choose $y$ maximal with this size at most $k$ and append higher binary positions to fill the remaining difference, one unit at a time. The new permanent rows have total reciprocal sum at least
$$
         g(A,L)+\sum_{p^j\le y}H_{p-1}/p^j .
$$
By the prime number theorem, $B(y)\sim F(y)\sim y^2/(2\log y)$, and the jump to the next integer cutoff is at most $y+1$. Thus $k\sim F(y)$. The exact-size zero-defect estimate in the [companion manuscript](anchored.pdf) gives $\sum_{p^j\le y}H_{p-1}/p^j=R_0(k)+o(1)$ uniformly in this regime. This proves the lower limit for every fixed prefix and hence for their supremum, including an infinite supremum.

For the upper bound, the Znám–Simpson digit budget for an irreducible cover gives $b(L)\le k-1$. The [first-position knapsack bound](anchored.pdf) gives $\Phi(L)\le R_0(k)+o(1)$ uniformly for all such periods. For completeness, select first prime positions with costs $p-1$ and values $H_{p-1}/p$ in decreasing value-to-cost ratio, which is the increasing prime order. Fractional relaxation loses at most the next term $o(1)$. All higher positions together are bounded by $\sum_pH_{p-1}/(p(p-1))$, which is convergent and attained up to $o(1)$ in the zero-defect construction. Also $L\ge k+1$ because it is the largest of $k$ distinct integers greater than one. Therefore $R_*(k)\le R_0(k)+\Gamma+o(1)$ when $\Gamma$ is finite. This proves the formula.

The same argument gives a limit and an identical finite-prefix characterization for any nonempty subclass of full-period prefixes closed under these ordinary extensions and the stated padding. For the disjoint cyclic constructions of [cycles.md](cycles.md), allowing ordinary one-digit extensions, this limit is finite by the chord-mass estimate and is at least $0.000704743307$. To see the lower estimate directly, use the finite quartets and install all ordinary prime powers up to a fixed cutoff above their largest required cofactor. The reciprocal mass of the prefix differs from $\Phi(L)$ by exactly the sum of the quartet gains. No limit over growing patterns is needed to realize this certificate.

For a genuine irreducible set that omits its least common multiple, removing an ordinary modulus can expose several holes of the full period. The two-hole and singleton property used for the free extension then requires separate proof. Establishing a loss bound for replacing such a set by a full-period prefix would link this variational formula to the unrestricted coefficient.
