# A strict reciprocal gain from a cycle of prime coordinates

Codex (OpenAI), at Jordan Pollard's request, 27 November 2026. AI-authored written proof for review.

Let $R(k)$ be the largest reciprocal sum of an irreducible set of $k$ distinct covering moduli and let $R_0(k)$ be the zero-defect optimum, as in the companion [manuscript](anchored.pdf). In particular both allow residues to be reassigned after any deletion. We prove
$$
\liminf_{k\to\infty}(R(k)-R_0(k))\ \ge\ 0.000704743307 .
$$
One quartet alone gives the exact strictly positive lower bound $931319/5803891632$. Moreover, for every fixed $b<0.000704743307$ there is a constant $c_b>0$ such that at every sufficiently large exact $k$ one irreducible set satisfies both
$$
 S\ge R_0(k)+b,\qquad M\le m_g(k)-c_b m_g(k)^{4/5}.
$$
Here $m_g$ is the best grouped-digit minimum. The [forest theorem](anchored.pdf) gives $R_0(k)+o(1)$ throughout its class. The sharp unrestricted leading coefficient and the unrestricted minimum remain open.

## A two-terminal construction and its converse

Take two distinct terminal coordinates and $r\ge2$ internally disjoint paths joining them. Every path has at least two edges. Coordinates are distinct primes $p_i\ge d$ with $d\ge2$. At each vertex use $p_i-d$ unary rows. At each path edge use $d-1$ pair rows. Put $t$ direct pair rows on the two terminals and allow one additional singleton specifying every coordinate. Each ordinary row fixes one tuple on its named support. Repeated internal supports are indexed. Their conversion to distinct moduli is given below.

**Theorem.** One can arrange a unique ordinary hole and the full family is indispensable under arbitrary reassignment if and only if $r=2$ and $t=(d-1)^2$.

**Path estimate.** Restrict each vertex to any $d$ allowed digits. A link with at most $d-1$ forbidden pairs contains a perfect matching. A failure of Hall on a set of $j$ digits would require deleting at least $j(d-j+1)\ge d$ pairs. For a path, use fixed perfect matchings on every link except one. They biject the endpoint alphabets with those of the exceptional link. Thus the set of impossible endpoint pairs of the path has size at most the number of rows on *any* chosen link.

**Separation at an interior vertex.** Suppose a path has a unique continuation between a pair $(a_0,b_0)$. Split at an interior vertex and write $L,R$ for the impossible endpoint pairs of the two nonempty halves, with the exterior endpoint listed first. Each set has size at most $d-1$. All but one intermediate digit are excluded by $L$ at $a_0$ or by $R$ at $b_0$. For $a\ne a_0$, $b\ne b_0$ there are at most $2d-2-(d-1)=d-1$ excluded middle digits because the two exterior rows of each relation are disjoint. Hence every such pair extends. More generally the sizes of the two middle fibres sum to at least $2d-|L|-|R|$. The precise finite estimate is kernel-checked in [PathSeparator.lean](PathSeparator.lean).

If the ordinary system has just one global hole, choose $d$ surviving digits at each vertex including its coordinates. Each path has a unique continuation on the surviving endpoint pair because its interior is disjoint from the others. Every pair differing in both endpoints therefore extends through *every* path simultaneously. Direct rows must prohibit all $(d-1)^2$ of those pairs. This gives $t\ge(d-1)^2$ for arbitrary path lengths and any number of paths.

For $r=2,t=(d-1)^2$, the path estimate leaves at least $d^2-2(d-1)-(d-1)^2=1$ feasible endpoint pair for every assignment. After a pair-row deletion, use the damaged link for its path estimate if it is a path row. There are then at least two feasible endpoint pairs. After a unary deletion, the affected vertex has at least $d+1$ surviving labels. Apply noncoverage once, exclude the coordinate of the hole just obtained there, choose $d$ surviving labels again, and reapply noncoverage. After singleton deletion noncoverage of the ordinary rows suffices.

For a covering assignment, use unary rows to retain labels $0,\ldots,d-1$. Orient the two paths to form a cycle. On each directed edge prohibit all $(u,0)$ for $u\ne0$. On the chord prohibit all pairs of nonzero digits. A surviving tuple containing a zero must be zero everywhere by propagation. An all-nonzero tuple violates the chord. The singleton fills the unique hole.

Extra chord rows can be removed while retaining this cover. If $r>2$, keep the first two paths as the cycle. At the forced terminal values $(0,0)$, force the interior vertices of each additional path to zero by orienting two arms **away** from the endpoints. On each arm forbid $(0,u)$ for all $u\ne0$. The two arms reach every interior vertex after omitting any chosen link of the path. All rows of that link can be discarded. Thus no larger $r$ gives an indispensable family. This last step allows all surviving rows to be rearranged.

## Distinct integer moduli

Suppose an earlier construction with period $L$ has one distinguished class modulo $L$, translated to zero, and the other classes leave exactly this class uncovered. Use fresh primes for the vertices. Dress each occurrence of an internal support of product $n$ by a divisor $a\mid L$, assigning zero modulo $a$ and the specified internal labels modulo $n$. Use different $a$ within each support. The new distinguished row has modulus $L\prod_i p_i$. Distinct internal supports are distinguished by their fresh primes.

The old ordinary rows always miss at least one residue of $L$. On a missed residue the active new rows project to a subfamily of the internal rows. Thus deleting a new ordinary row leaves at least two internal holes on the same old residue. Deleting an old ordinary row leaves at least two old residues under arbitrary reassignment, by the inductive singleton property. On each of them the internal family leaves at least one hole. Deleting the new singleton also exposes a hole. This proves arbitrary-reassignment irreducibility and the strengthened two-hole condition for another substitution. Powers of two already suffice as initial dressings if only existence is desired. The following dressings give the reciprocal gain.

## Exact positive mass

Set $d=2$ and use two paths of length two. Write four consecutive odd primes as $a<b<c<e$. Use $a,b$ as terminals, $c,e$ as the internal vertices. All five products of two primes except $ce$ occur, each with cofactor one. On $p$ use $p-2$ unary moduli dressed with the smallest $p-2$ available integers having every prime factor smaller than $a$. This is done after all needed powers of the preceding primes have been prepared. On each group the gain relative to the four ideal ordinary first positions is exactly
$$
 g(a,b,c,e)=\sum_{uv\in E}\frac1{uv}
 + \sum_{p\in\{a,b,c,e\}}\frac1p
 \left(\sum_{j\in D_p}\frac1j-H_{p-1}\right).
$$
Here $D_p$ is the indicated set of dressings. One quartet adds exactly one ordinary row to the four first-position counts.

For $(37,41,43,47)$ the dressings change from $[1,p-1]$ as follows.

| Prime | Removed | Added |
|---|---|---|
| 37 | 36 | |
| 41 | 37 | |
| 43 | 37, 41 | 44 |
| 47 | 37, 41, 43 | 48, 49 |

The formula gives $g=931319/5803891632>0.0001604$. For any fixed disjoint quartets of consecutive primes the gains add. All products for an earlier stage are supported on earlier primes. After the four first positions, install all needed higher positions of the four primes in increasing prime order with their usual dressings $j<p$. For the quartets used here $p<2a$, so the missing higher powers of the four primes could not occur in any of those dressings. All later stages recover the same period as in the ordinary construction. The new first positions are distinct from higher positions since their exponents on the four primes are zero or one. This verifies that the comparison accounts for every changed row.

[diamond_gain.py](diamond_gain.py) exhibits 2,395 disjoint quartets with primes through 100,000 for which the sum of the gains exceeds $704743307/10^{12}$. The program rounds *each* individual gain down to a multiple of $10^{-12}$, then maximizes the sum of these integers on disjoint intervals. Its recurrence either skips the last prime or appends the quartet ending there to a solution on the first $i-4$ primes. Only the exhibited lower bound is needed. Up to the largest cofactor used in each selected quartet, every composite is available because it is below $2a$ and has all prime factors less than $a$. An independent direct factorization and full harmonic-sum calculation through 300 gives $0.0005872768204\ldots$ already. A second program uses trial-division primes, a binary search for the dressing cutoffs, and integer upper and lower bounds for ordinary harmonic prefixes. It verifies the total gain of all 2,395 quartets is at least $704744497146696330988/10^{24}$. [Independent full certificate](independent_gain.py)

Lean 4.33.1 independently evaluates the complete old and new rational sums at the first quartet and checks their exact difference. [DiamondGain.lean](DiamondGain.lean)

To use these fixed substitutions at *every* sufficiently large exact size, take the stages, cap and overlapping size intervals of the [forest construction](anchored.pdf). For large enough $z$ every designated star prime exceeds all the finitely many quartet primes, all the required small prime powers are installed, and each modified modulus is below the cap. In the ordinary preparation prefix replace exactly the consecutive first positions described above and postpone their higher positions until immediately after these four first positions. This preserves the period at the end of each group. All later rows and their weights remain as prescribed. The intervals of attainable sizes shift by the fixed number of quartets, including at successive $z$. Their overlaps persist. The proof comparing the old cap to $m_g(k)$ uses the surplus of order $z^{8/5}/\log z$, so this fixed shift preserves the four-fifths conclusion. Their baseline reciprocal weight $U_z$ still satisfies $U_z=R_0(k)+o(1)$ uniformly, since $k\sim F(z)$. The losses from the much larger forest primes are $O(\delta)+o(1)$. Given $b$ below the certified gain, take the fixed band width $\delta>0$ small enough. This proves both claims.

## Bounds within this cyclic construction

For $r=2$ the two paths form one cycle on $n$ vertices. Relative to $\sum_i(p_i-1)$, the $n$ unary groups and $n$ path edges balance exactly. The excess is the $(d-1)^2$ direct rows. If the moduli have cap $X$, the two terminal primes $a\le b$ give
$$
 (d-1)^2\le \min\{a^2,X/(ab)\}\le\min\{a^2,X/a^2\}.
$$
For disjoint gadgets, their smaller terminal primes are distinct. Summing over all primes $a$, splitting at $X^{1/4}$ and using partial summation with $\pi(u)\ll u/\log u$, gives $O(X^{3/4}/\log X)$ surplus independent of path length. This is below the established forest scale.

There is also an absolute ceiling on the reciprocal improvement for disjoint gadgets at first prime positions. Write $s=d-1$. Unary rows lose at least $s/p^2$ at $p$ relative to $H_{p-1}/p$. The path-edge rows have total mass at most $H_s\sum_p1/p^2$ on the cycle, using $2/(pq)\le 1/p^2+1/q^2$. The chord adds at most $H_{s^2}/(ab)$. For $s\ge4$, $2(s-H_s)\ge H_{s^2}$. At $s=4$ it follows directly. In the step to $s+1$ the right side increases by at most $(2s+1)/(s^2+1)$ whereas the left side increases by $2s/(s+1)$, which is larger for $s\ge4$. The allowances at just the two terminals absorb the whole chord. For $s\le3$ the uncompensated sum over disjoint chords is bounded by $(H_9/2)\sum_p1/p^2$. The first-position baseline therefore exceeds all but a bounded amount of the actual reciprocal sum; ordinary higher positions and the terminal row are accounted for as in the forest theorem. A leading-coefficient gain requires other interactions.

## Verification and sources

The independent exhaustive computation in [cyclic_check.py](cyclic_check.py) treats all 1,024 assignments on the residual binary diamond. There are 32 assignments with one hole. After deleting a path row the minimum is three holes, and after deleting the chord it is two. It also enumerates all 485,809 pairs of residual link relations at $d=4$, including inactive and repeated forbidden rows through their effective sets. The Boolean mask interpretation, all 1,024 assignments, deletion masks and canonical singleton also passed Lean kernel replay. [Lean profiles](BinaryProfiles.lean) · [Output](cycle-finite.txt). The path and all-size theorems have written proofs. Human peer review and priority remain pending.

The original problem is due to Erdős and Graham. The order of growth of the unrestricted reciprocal maximum is known. Star Fleet Math credits Wouter van Doorn for the logarithmic-order construction. Öztürk gives the relaxed upper coefficient. Karve and Hirani classify binary graphs admitting an unsatisfiable choice of edge clauses. Their theorem includes the universal satisfiability property for the binary diamond. Our counting argument also gives the arbitrary-alphabet result and the obstruction to adding further paths. [Original problem](https://www.erdosproblems.com/1189) · [Öztürk](https://www.researchgate.net/publication/413884122) · [Star Fleet Math](https://www.starfleetmath.com/) · [Karve and Hirani](https://doi.org/10.1016/j.dam.2019.12.017)
