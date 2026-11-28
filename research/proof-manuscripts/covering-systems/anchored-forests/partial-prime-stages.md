# Conditional branching for a prime group with twice its ordinary size

Codex (OpenAI), November 28, 2026. Written construction for Erdős #1189.

Fix $t>0$. There exist zero-defect irreducible covering sets with $X\sim k\log k$, $S=R_0(k)+o(1)$ and a prime $p\sim\sqrt X/5$ owning exactly $2p+1$ eligible rows in the [critical sieve](batch-cap-sieve.md), at $Y=\sqrt X\exp(-t\sqrt{\log X})$. For every reserved row, partition and common complementary assignment, one of its two complete batches has
$$
                      \log b(B)\ \ge\ p^{1-o(1)}.
$$
The maximum possible exponent of p in this logarithm is one: every batch cofactor is at most X, so $\log b(B)\le p\log X=p^{1+o(1)}$ in this regime. Thus even the optimized projection achieves the sharp *exponent* in a single heavily overfilled group, on the leading cap scale and at essentially ideal reciprocal mass. The bounds do not give an asymptotic constant for the logarithm.

Choose a prime $z\sim5p$. Let $A=\lfloor p^{2/3}\rfloor$, $C=\lfloor p\exp(-2t\sqrt{2\log p})\rfloor$. For primes $A<r\le C$ set capacities $m_r=\lfloor4p/r\rfloor$. Their total is $(4\log(3/2)+o(1))p>p+2$, by the prime reciprocal sum, with total rounding error $O(\pi(C))=o(p)$. The subtotal on $(C/2,C]$ is $O(p/\log C)=o(p)$. Choose integers $0\le u_r\le m_r$, saturated on $(C/2,C]$, whose sum is exactly $p+2$. Greedy filling of the lower interval suffices. We have $u_r\le4p/A=o(A)$.

Start with all positions $s^j\le z$ having prime base $s\le A$, using the usual $s-1$ moduli $s^jd$ with $1\le d<s$. Let M be their period. Install the p-stage with $p-1$ distinct old divisors d through $4p$ as guards. Through $4p$ the fraction lost to a prime above A is at most $\log(3/2)+o(1)$ and every smooth integer here divides M for large p since $4p<z$. This leaves more than p divisors. Next install all primes $A<r\le C$ in increasing order. At r use the following $r-1$ moduli:
$$
   rd\quad(1\le d\le r-1-u_r),\qquad
   prd\quad(1\le d\le u_r).
$$
For the first list, all factors needed for $d<r$ have already been installed: primes above A occur at most to exponent one since $A^2>z$. For the second list d divides M since $u_r<A$. Complete the unused positions through z with the ordinary digit stages and the z-terminal guards, exactly as in the [two-batch construction](optimised-batch-visibility.md). Ordered stages prove distinctness, coverage and irreducibility for all reassignments there. All special moduli are at most $4p^2<z^2$ and $X=z(z+O(1))$. Thinning retains every one of the $p-1+\sum u_r=2p+1$ p-owned rows because their second prime is at most $C<Y$ or at most A. A different prime in the bin of p has at most its ordinary allowance, and z is in a different bin.

Fix a reservation, partition and complementary assignment. Both complete p-batches exist, and at most one of the original p-owned rows is outside their union, counting even the reserved row. Choose an old surviving point modulo M, and a p label avoiding the outside p-owned row and the terminal guard at $zp$ if either is present. At each r and above **each particular earlier surviving prefix obtained this way**, at most $r-1-u_r$ unmarked rows can forbid a next label. All p-owned rows here are absent or miss. Thus there are at least $u_r+1$ surviving choices. Every branch extends through the ordinary stages, and the terminal misses some label because $zp$ is absent or inactive. This proves conditional branching even after fixing all smaller prime coordinates along a branch.

For either batch, keep only the digits of the r's it tests. At each retained r the above choices multiply the number of distinct retained patterns by at least $u_r+1$: take one concrete extension for every earlier retained pattern and branch from it. At other levels retain at least one extension. Every r in $(C/2,C]$ occurs in at least one of the two batches, since $u_r=\lfloor4p/r\rfloor>1$. Hence
$$
 \max_B\log b(B)\ge\tfrac12\sum_{C/2<r\le C}\log(1+u_r)
             \gg \frac{C\log(p/C)}{\log C}=p^{1-o(1)}.
$$
Unlike prescribing every label, this proof permits the available labels to depend on all previous choices.

For the same cardinality as the ordinary construction, the reciprocal loss at the p stage is at most $H_{p-1}/p=o(1)$. At a partially transferred r stage only the largest $u_r$ ordinary cofactors were removed; their total reciprocal mass is at most $u_r/[r(r-u_r)]$. Across all r the loss is $O(p/A^2)=o(1)$, while the new moduli have positive mass. Zero-defect optimality and the cutoff estimate finish the two size and reciprocal claims. Only one owner carries the extra p rows, so this does not produce the widespread excess required by [the weighted obstruction](owner-excess.md).

[Exact conditional branching tests](partial-stages-check.py). The general result is written.

**Exact small instance.** For the 57 moduli of maximum 936 in the check, take the two 13-batches before arithmetic thinning (also valid whenever $Y\ge11$). At 5 and 7 all labels are free. At 11, four ordinary rows each forbid at most one label and a fifth ordinary row, of modulus 55, tests just one pair of labels at 5 and 11. At least $5(11-4)-1=34$ pairs survive, for every value at 7. At least seven labels at 11 occur if the 5 coordinate can be chosen freely. After any reservation and partition each of the three donor primes still occurs in the two batches together; only one original 13-owned row is outside, and each donor has at least four special rows. Some batch sees a pair. The minimum counts forced by the respective pairs are 35 for $(5,7)$, 34 for $(5,11)$ and 49 for $(7,11)$. Thus the larger visibility is at least 34 under every complementary assignment. An explicit partition and assignment attain counts 34 and 7, giving exact optimum 34. The check independently scans the full integer period 12,252,240 and all 805,255 assignments of the four universal labels and the extra pair. This illustrates a lower bound after conditioning on the smaller prime and includes full reassignment after deletion.
