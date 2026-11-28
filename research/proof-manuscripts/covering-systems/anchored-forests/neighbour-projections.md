# The earlier holes can be detected on prime factors of the current rows

Codex (OpenAI). Written supplement to the [prime-coordinate erasure theorem](projected-holes.md) for Erdős #1189. The earlier theorem projects the holes onto all surviving earlier primes. Here the witnessing coordinates must occur in the current rows themselves, and can be bounded away from the current prime by a fixed power.

**Theorem.** Fix $\epsilon>0$. There exist $a,\delta,\theta,\lambda>0$ such that the following holds for all sufficiently large $k$ whenever an irreducible set of $k$ moduli has reciprocal sum at least $(1/2+\epsilon)\log k$. Reserve any one row. There is a set of primes $k^\delta<p\le k$ of total reciprocal mass at least $\lambda$, selected before any residue assignments, with the following property at every such $p$.

Take the unreserved rows $pc$ whose largest prime is $p$ and in which $p$ occurs once. Discard any of these rows with total **cofactor** reciprocal mass $\sum 1/c\le\lambda\log k$. Of the remaining rows keep only those with $c\le k$. Let $Q$ be the prime factors of these cofactors in the range
$$
                          k^a<q<p^{1-\theta}.
$$
Erase any further set $E$ with $\sum_{q\in E}1/q\le\lambda$. For every assignment of the earlier unreserved rows (all their prime factors strictly less than $p$), the uncovered residues have at least $k^a$ distinct patterns modulo the primes in $Q\setminus E$. All these are first-digit patterns. In particular $\sum_{q\in Q}1/q>\lambda$, even after the allowed row deletions. The stronger pattern conclusion is about the actual uncovered residues of the old system, under unrestricted reassignment.

**Proof.** In the notation of the [earlier proof](projected-holes.md), select the good positions with $W_p\ge H_{p-1}+\eta\log k$ and positive total reciprocal mass. For an arbitrary collection $A$ of retained cofactors put $C=\operatorname{lcm}_{c\in A}c$, and apply its position estimate to these cofactors using any $g\mid C$. Precisely,
$$
     \sum_{c\in A}1/c\le H_{p-1}+\log|H\bmod g|+O(1+\log(2+s)),
$$
where $s$ counts primes dividing $C$ but not $g$ and $H$ is still the set of **original earlier holes**. No change to the earlier moduli is necessary. The finite group bound in that proof uses only that $gv\mid K'$ for every attained $v=c/\gcd(c,g)$, which holds since $gv\mid C\mid K'$. The second-moment estimate need only sum over primes in $C$. This proves the restricted version.

Cofactors $c>k$ cost at most one, by the count of rows. For a prime $q$, all cofactors divisible by $q$ have total mass at most $H_k/q$: after division by $q$ the resulting positive integers are distinct. Thus removing all rows touching the further erased set costs at most $\lambda H_k$. Rows touching a prime $p^{1-\theta}\le q<p$ cost at most
$$
                    H_k\bigl(-\log(1-\theta)+o(1)\bigr).
$$
This follows from Mertens' prime reciprocal sum, uniformly for $p\ge k^\delta$ with fixed $\theta$. Choose $\theta,\lambda>0$ small relative to $\eta$ and decrease $\lambda$ to fit the mass of good positions. After these deletions, the surviving collection $A$ still has cofactor mass at least $H_{p-1}+(\eta/2)\log k$ for large $k$. Take $g$ to be the product of all primes in $C$ greater than $k^a$. There are at most $k^a$ primes of $C$ missing from $g$. Hence
$$
 (\eta/2)\log k\le \log|H\bmod g|+ O(1+\log(2+k^a)).
$$
Choose $a>0$ small in terms of $\eta$, the absolute constant, and $\delta(1-\theta)$. We obtain $|H\bmod g|\ge k^a$. Every prime dividing $g$ belongs to $Q\setminus E$. Projection on that larger set can only increase the count. If $Q$ had reciprocal mass at most $\lambda$, erasing all of $Q$ would leave just one pattern, a contradiction.

The eligible partners can therefore be detected from the moduli $pc\le pk$ alone, before looking at the earlier residues. It remains open whether the simultaneous requirement on the earlier holes prevents a coefficient above $1/2$. This proof uses the classical prime reciprocal sum and the position estimate, with credits and exact finite checks in the [main note](projected-holes.md). A [separate enumeration](neighbour-projections-check.py) verified the group capacities on 30,786 subcollection and projection choices, and the cost of erasing each subset of partner primes in the same example.
