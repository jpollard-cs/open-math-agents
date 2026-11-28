# Almost every row can belong to an unavoidably large batch projection

Codex (OpenAI), November 28, 2026. Written companion to the [two-batch construction](optimised-batch-visibility.md) for Erdős #1189.

Use the [same cap sieve and its quantifiers](batch-cap-sieve.md). Given any fixed $t>0$, there are zero-defect irreducible covering sets with $X\sim k\log k$ and $S=R_0(k)+o(1)$ such that, at
$$
                        Y=\sqrt X\exp(-t\sqrt{\log X}),
$$
at least $(1-o(1))k$ of the actual rows lie in complete batches B satisfying $b(B)\ge Y/3$ (for sufficiently large parameters). This holds for **every** reservation and partition, and in **every** common complementary assignment for each bin. Each of these batches contains a modulus $pr$ with largest prime p, and every residue modulo its specified cofactor r occurs among the holes. In each bin the first labels of *all* the associated donor primes r can vary jointly and independently. The holes can come from different integers. The choices of assignments for different bins may be independent.

The examples attain the leading cap and reciprocal lower bounds. They show that controlling the number of rows in large-projection batches, even after optimizing the partitions, is insufficient for the unrestricted minimum. The difference between the number of rows owned by p and its ordinary allowance $p-1$ is exactly one at each recipient in this construction. That distinction gives the [weighted obstruction](owner-excess.md).

## Selecting the primes

Let z tend to infinity through primes, write $Z=\log z$, and put $A=\lfloor(2/5)z\exp(-t\sqrt{2Z})\rfloor$. Take candidate recipient primes in
$$
                     z/Z\le p\le z(1-Z^{-1/4}).
$$
Split these candidates into dyadic prime bins. Within each bin partition as many as possible into disjoint blocks of size $r-1$, using a different prime $r\in(A,2A]$ for each block across all bins. One can take the r's in increasing order and leave fewer than $2A$ candidates unused in each bin. There are enough donors: at most $O(z/(AZ)+\log z)$ are needed (in fact there are only $O(\log Z+1)$ relevant bins), whereas $(A,2A]$ contains order $A/\log A$ primes. All donors are below every recipient. Assign to every member p of each block its donor r.

The sum of p over selected recipients is $(1-o(1))\sum_{p\le z}p$. The excluded low interval costs $O(z^2/Z^2)$ even by summation over all integers up to $z/Z$. For the upper interval, the prime number theorem at both ends gives $o(z/Z)$ primes, each at most z. In all bins together the unfilled blocks lose $O(zA\log Z)=o(z^2/Z)$. These estimates and $\sum_{p\le z}p\sim z^2/(2Z)$ prove the assertion.

## Construction and verification

Start with the ordinary digit stages for $M=\operatorname{lcm}(1,\ldots,A)$. Install each selected p with $p-1$ moduli $pd$, taking for d the smallest $p-1$ divisors of M. Each chosen d is at most z. Indeed the number of integers through z lost to a prime above A is at most $z\sum_{A<\ell\le z}1/\ell=O(z/\sqrt Z)$, using the classical prime reciprocal sum with error $O(1/\log A)$. Loss to proper prime powers above A is $O(z\log A/\sqrt A)$: for bases larger than $\sqrt A$ sum their reciprocal squares and higher powers, and for smaller bases the tail starting above A is $O(1/A)$ per base. These losses total less than $z Z^{-1/4}$ eventually. Thus the ordinary recipient stages fit below cap $z^2$.

For each donor r use its $r-1$ assigned moduli $rp$, one per member of its block. These are its only first-digit stage rows. Now append the remaining positions $s^j\le z$ in increasing prime, then exponent order, using the usual guards $1\le d<s$. End with the z terminal rows and guards from the [two-batch construction](optimised-batch-visibility.md). Each required guard divides the preceding period. Each ordinary stage has exactly one fewer row than its radix, all testing the new digit, and the terminal guards have lcm the full old period. The same surviving-child and terminal argument proves coverage and irreducibility under arbitrary residue reassignments. Each row is distinct, and $X=z(z+O(1))$ as before. In particular $A/Y\to2/5$ and $2A<Y$ eventually.

At each recipient p there are exactly p rows with largest prime p, its original $p-1$ and its single $pr$. The factor r and all prime factors of the p-stage guards are at most $2A<Y$. These rows survive both thinning rules. Every intact p group is therefore a forced complete batch under every partition. The reserved row can break at most one such group. Other first-position groups have at most their ordinary allowance, except possibly the terminal z. Removing additional complete batches only enlarges the holes.

Fix a bin containing an intact recipient batch and assign all complementary rows arbitrarily. Choose an old surviving point modulo M. In every intact recipient of this bin there are no remaining p-owned rows. In a recipient of the bin broken by reservation there are at most $p-1$ remaining p-owned rows in total: choose its p label avoiding the labels of all of them, including its donor row when present. In the other bins the ordinary p stage has at most $p-1$ rows, so choose a surviving label. Pick one intact p in the chosen bin and avoid the p label of the terminal row $zp$ if present. The guard p at z exists since $p<z$.

Now prescribe arbitrarily the joint first labels at every donor belonging to the chosen bin. Its rows were all removed or neutralized by the choice at the broken recipient. Donors for the other bins still have at most $r-1$ constraints and can each be given a surviving digit. All subsequent ordinary stages admit a surviving child over every earlier choice. At most $z-1$ terminal rows are active because $zp$ misses or is absent. This constructs the requisite integer. An intact batch tests its donor r, so $b(B)\ge r>Y/3$ eventually. The sum of these intact batch sizes is $(1-o(1))k$, losing at most z from reservation. Conversely the aligned old M leaves one class there. Reserving a terminal row realizes $b(B)=r$ simultaneously within each bin for every recipient, since its guard lcm divides $Mr$.

The size is exactly $1+\sum_{s^j\le z}(s-1)$ as in the preceding theorem. For the reciprocal mass, an ordinary recipient stage loses at most
$$
 \frac1p\sum_{d<p,\ d\nmid M}\frac1d
       \ll \frac{1+\log z}{p}
          \left(\sum_{A<\ell\le z}\frac1\ell+
                 \sum_{\ell^j>A,\ j\ge2}\ell^{-j}\right)
       \ll \frac{\sqrt Z}{p}.
$$
Taking the smallest divisors retains the contributions of every $d<p$ dividing M. The sum of $1/p$ over recipient primes is $O((1+\log Z)/Z)$ by the prime reciprocal sum. Together the recipient stages cost $o(1)$. The discarded ideal mass at all donor stages is $O((z/(AZ)+\log z)(\log A)/A)=o(1)$. All other positions retain their ideal mass. The zero-defect estimate proves $S=R_0(k)+o(1)$.

The loss of coverage after deleting all rows divisible by large marked primes and the number of visible cofactor classes answer different extremal questions. This construction determines that the possible upper limit of the **fraction of rows** in batches with visibility at least $Y/3$ is one, under every reservation and optimal complementary assignments at this critical sieve cutoff. It supplies no improvement in the leading constant of the unrestricted minimum.

[Reproducible finite example and arithmetic checks](donor-batch-check.py). The asymptotic and arbitrary-assignment arguments are written.

In the finite check the radices 11 and 13 use the common donor 3, with donated rows 33 and 39. The 52 distinct moduli have maximum 3400 and period 1,458,600. At most one of the two batches can be broken by reservation and each intact batch sees all three donor labels. The written proof permits arbitrary complementary placements. The code also tests all 52 reservations on one explicit assignment by direct integer enumeration.
