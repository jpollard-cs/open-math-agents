# A cap bound from the supports tested together in a block

Codex (OpenAI), November 27, 2026. AI-authored written companion to [Mutual dependence in a cover with one uncovered residue](component-surplus.md).

Let $D$ be any irreducible set of $k$ distinct moduli with largest modulus $X$. Its lcm need not be a modulus. Reserve any one row. Partition the prime-digit positions of the lcm into ordered nonempty blocks. Assign each remaining row to the last block it tests, and call its set of tested positions there its internal support. For a given block and nonempty support $I$, write $t_I$ for the number of these rows. For any assignment of all rows in earlier blocks, project the old uncovered points onto the union of the earlier positions tested by the $t_I$ rows. Write $b_I$ for the least possible number of different projected patterns over those earlier assignments. In particular $b_I=1$ if the rows have no earlier tests. Assignments attaining these bounds can differ for every group. Prefixes which are shorter than the digits used by a modulus present no difficulty: the full CRT digit grid supplies all earlier and later coordinates independently.

Let $A\ge1$ be a fixed bound on $b_I$ for singleton internal supports and $B\ge1$ a bound for larger supports. Charge each distinct larger support to a position in it of smallest base prime, breaking ties in any fixed way. Let $h$ be the maximum number of distinct supports charged to one position, and take $h=0$ if there are none. For every fixed $0<\eta<1$, uniformly for $1\le B\le X^{1-\eta}$,
$$
 k\ \le\ 1+\sum_{p\le\sqrt X}\min\{Ap-1,\lfloor X/p\rfloor\}
   +O_A(X^{2/3}\log X)
   +O_\eta\left(\frac{h B^{1/4}X^{3/4}}{\log X}\right).
$$
For fixed $A$ the prime sum is $(1+\log A+o(1))X/\log X$. In particular if the unaries see one old pattern and $h^4B=o(X)$ under the indicated envelope, then $k\le(1+o(1))X/\log X$. With $A=1$ that prime sum is exactly $F(\sqrt X)=\sum_{p\le\sqrt X}(p-1)$. The familiar ordinary digit constructions attain the leading constant at every sufficiently large exact size and admit this decomposition: take their ordinary digit stages and reserve their final row. These hypotheses put no bound on the total number of earlier holes or on the number of boxes covering the grid.

**Finite group capacity.** Earlier rows must leave a hole under every assignment since they omit the reserved row. With $P(I)=\prod_{i\in I}p_i$ there are $b_I P(I)$ combinations of an earlier projected pattern with the internal tuple. Given at least that many rows of this group, aim a different row at each combination. Within the earlier tests of that row prescribe the chosen old values and on $I$ prescribe the internal tuple. It has no other tests. Every extension of an earlier hole would then be covered without the reserved row. Irreducibility under arbitrary reassignment therefore implies $t_I<b_I P(I)$. Each modulus is divisible by $P(I)$, even when several digit positions have the same prime, and also by $m(I)$ defined in the main note. Global distinctness gives $t_I\le X/m(I)$.

At the highest digit $(p,e)$ the rows fixing it have at least $p$ different moduli: the rest have a hole, or are empty, and changing that one digit leaves a whole fibre for those rows to cover. Thus $p^{e+1}\le X$. At first positions the singleton groups contribute at most the prime sum above. At higher positions $p\le X^{1/3}$, each contributes at most $Ap$ and there are at most $\log_2 X$ positions per prime. This gives the first error term. For the fixed-$A$ evaluation split at $\sqrt{X/A}$ and use the prime number theorem and partial summation in the fixed-ratio interval above the split. The $O_A(1)$ loss per prime from floors and the subtraction of one is negligible; the two leading contributions are $X/\log X$ and $(\log A)X/\log X$. When $A=1$ use $p-1\le X/p$ directly.

For a support charged to a position with base $p$, we have $m(I)\ge P(I)\ge p^2$. Its count is at most $\min(\sqrt{BX},X/p^2)$ by the two finite bounds. Put $z=(X/B)^{1/4}\ge X^{\eta/4}$. The total number of positions whose base is at most $z$ is $O_\eta(z/\log X)$: bases through $\sqrt z$ contribute $O(\sqrt z\log X)$ and above that point each prime has at most $2\log X/\log z$ positions. For $p>z$ the number of positions is also $O_\eta(1)$ and $\sum_{p>z}1/p^2\ll 1/(z\log z)$ by partial summation. Hence the total charge is
$$
 O_\eta\left(h\sqrt{BX}\,z/\log X+hX/(z\log X)\right),
$$
as claimed.

For example, suppose $A=B=1$ and a family gains $cX^{4/5}/\log X$ rows above $F(\sqrt X)$. Every qualifying decomposition must charge at least $c'X^{1/20}$ different supports to some one digit. For internal supports of size at most two this requires that many directly co-tested digits. The known [forest construction](anchored.pdf) reaches the four-fifths scale along its caps. This corollary rules out spreading its gain evenly among bounded-degree pair interactions even when the earlier dressings can use arbitrary primes.

The general fixed-size minimum remains open. The estimate does not assert that arbitrary irreducible sets have a decomposition satisfying the bounds on $A,B,h$. The separate [finite check](component-cap-check.py) tests the group inequality by direct congruence placements and exhausts the permitted old assignments in its small-period cases.

On four independently tested integer sets, the check completed 6,016 groups over 1,715 block-order and reservation choices. Of these groups, 2,708 saw multiple old patterns and 1,338 attained the strict integer capacity minus one. One of the four sets has period 60 and largest modulus 30.
