# Overfilled prime fibres and a bound on period propagation

Codex, at the request of Jordan Pollard. AI-authored written proof for review. Companion to [the construction with complete prime-product boxes](saturated-boxes.md).

Consider the same bipartite family of distinct prime coordinates. At each of the left primes pᵢ use pᵢ−bᵢ unary rows, leaving at least bᵢ≥2 values. A right prime q has q−a unary rows and tᵢ pair rows on each edge from pᵢ. Write D=Σtᵢ and s=D−a≥0. A right vertex *excludes* a surviving left vector if its unary and active pair rows cover all values of that right coordinate. The Chinese remainder theorem makes this the exact test for a cover: every surviving left vector must be excluded by some right vertex. The assigned residues on all indexed rows can vary freely.

## Which vectors can one right vertex exclude?

Two left vectors x,y can be excluded together for some assignment at this vertex if and only if

$$
  W(x,y)=\sum_{i:x_i\ne y_i} t_i\le 2s .
$$

Indeed at most s pair rows can be inactive at either vector. Each of the W disagreeing rows is inactive at least once. Conversely use distinct right unary residues. The D−W common rows can cover the same min(a,D−W) right values at both vectors. The remaining e=max(0,W−s) right values require that many of the W disagreeing rows at each vector. They can be assigned disjointly when 2e≤W. This proves sufficiency, including W=0 and e=0. There is no restriction on the other vectors excluded by this assignment.

Now take tᵢ=t for every left prime, and choose a divisor v≥2 of t. Put u=t/v and a=(h−1)t+u for h left primes, so that the slack is t−u. Take q≥a. Two excluded vectors differ in at most one coordinate. Consequently any set of at least two excluded vectors lies on a single coordinate line: a point off the line of two vectors differing on i also differs outside i, and on i differs from at least one of the two.

On a line varying i, at most (h−1)t right values can be covered by rows on fixed coordinates. Each excluded vector on the line needs at least u more active rows, and these rows are disjoint as the varying value changes. Thus at most v vectors are excluded. Conversely any v chosen values on a single line can be excluded: use the fixed-coordinate rows on (h−1)t distinct right values, then assign u varying-coordinate rows at each chosen value to cover the same remaining u right values. Subsets of size at most v can be covered in the same manner.

## A sharp threshold and essentiality with positive slack

Let P=∏bᵢ and suppose the grid of bᵢ left values can be partitioned into v-element subsets of coordinate lines. A sufficient elementary condition is that some bᵢ is divisible by v. With the parameters above the minimum number of right primes needed is exactly P/v. At this number **every indexed row is indispensable under arbitrary reassignment**, including every pair row, although each right prime has t−u more pair rows than remaining right values.

The capacity bound proves necessity. For sufficiency assign the right primes to the parts of the partition and use the indicated assignments. Conversely at exactly P/v right primes, coverage forces a partition into such line segments, since all capacity must be used. Thus the partition condition is also necessary for equality. When h=2 and b₁≤b₂, the grid is the edge set of the complete bipartite graph on parts b₁,b₂. Its v-element line segments are copies of the v-edge star. The classical theorem of Yamamoto, Ikeda, Shige-eda, Ushio and Hamada gives equality exactly when either b₁≥v and v divides b₁b₂, or b₁<v≤b₂ and v divides b₂. The graph decomposition result is theirs. [Original paper, Hiroshima Mathematical Journal (1975)](https://doi.org/10.32917/hmj/1206136782).

It remains to test all deletions. A missing left unary increases the lower bound for the number of surviving vectors above P. A missing right unary forces at least a+1 surviving values there. Its Hamming diameter is still at most one, and each vector on a varying line then needs u+1 rows among the t available. This excludes at most v−1 vectors. A missing pair row reduces the total to ht−1 and the slack to t−u−1. Any difference in at least two coordinates has weight at least 2t−1>2(t−u−1). On a line varying the damaged coordinate the remaining t−1 local rows supply at least u per excluded point. On a line varying an undamaged coordinate the t local rows must supply at least u+1 per point. Either way the capacity is at most v−1. Singleton excluded sets already satisfy this bound. Thus every deletion leaves a vector not excluded anywhere. Independent choices at the right coordinates give an actual hole for every reassignment.

At equality there are Σ(pᵢ−bᵢ)+Σqⱼ+(t−u)P/v indexed rows. Their excess over one plus the prime-digit cost Σ(p−1) is

$$
 (1+t-u)P/v-1-\sum_i (b_i-1).
$$

The distinct-integer substitution in the companion note applies unchanged by attaching suitable distinct exterior cofactors with the specified lcm. Existence of such cofactors for any given finite packet can also be forced with a sufficiently long binary-power chain when all internal primes are odd: use distinct powers of two within each repeated support, dress one terminal row by the largest binary power, and attach the packet on the unique uncovered binary class. This statement places no bound on the resulting maximum.

## Rigidity and the obstruction to carrying the period

At equality every covering assignment has exactly bᵢ surviving left values: any extra value would exceed the total capacity. Every right prime excludes exactly v vectors. Its right unary residues must be distinct by the a+1 argument, and its v vectors form a segment on a line. At these vectors all (h−1)t fixed-coordinate rows must be active and use distinct surviving right values. Otherwise each of the v points needs at least u+1 rows from the varying coordinate and v(u+1)>t. The t remaining rows are partitioned into v groups of u, one group per segment point. Each group uses precisely the same u residual right values. These conclusions hold for **every** covering assignment, up to the choices of the segments and labels.

At any left vector x, even outside the original surviving grid, let d denote the number of fixed coordinates disagreeing with the line of this right vertex. Let I=1 when its varying coordinate is one of that segment's v chosen values, and I=0 otherwise. The number of uncovered values at this right prime, using just its unary and pair rows, is exactly

$$
                      dt+(1-I)u.
$$

This follows because the fixed-coordinate rows cover disjoint blocks of t residual values, and the last u values are covered together or missed together. In particular a right vertex that does not exclude x leaves at least u values.

**If u≥2, no successful single-row refinement can carry two different right primes.** More precisely, replace any collection of these rows by single classes modulo positive multiples of their respective original moduli. If the refined family covers under any assignment, each refined modulus is divisible by at most one of the original right primes. A refined left unary modulus is divisible by none of them.

To see this, enlarge the assigned refined classes back to the original moduli and use rigidity. A refined row must contain the entire set of points covered exclusively by its enlarged row, since the other rows have only become smaller. For a pair row at right vertex j choose a segment point of j where the row is active. The missing right value there is private to that row at j. For a right unary row choose any point of the same segment and its unary value, which every active pair row misses. In both cases every other right vertex leaves at least u choices, independently. Vary each such digit while keeping all the others fixed. CRT supplies private integers with at least two different residues at that right prime, so it cannot divide the refined modulus. For a left unary row, choose its own unary value and surviving values at all other left primes. This vector lies on no excluded segment: the varied coordinate either disagrees with a fixed coordinate or is absent from the varying choices. Every right prime then leaves at least u values, independently. The same argument forbids them all. This proves the assertion for simultaneous refinements, including moduli with other prime factors or higher powers.

It follows that at least P/v refined rows are needed to carry all P/v right primes between them within the packet. The claim concerns rows of the packet itself. In a larger cover an older exterior row may have additional refinements. In particular a construction that passes the whole old period through one distinguished row cannot use such a packet with two or more right primes at this step. Conversely a single congruence per originally indexed row suffices with no refinement, so this is an obstruction to the proposed propagation, not an impossibility of these covers. At u=1 the lower bound on uncovered right values drops to one, and the same argument no longer forces distinct residues.

## Simultaneous overfilled boxes

The quantitative construction in the companion note also works with these positive-slack packets. In its notation take bᵢ=2, v=2, t=2 floor(z^(1/4)/2), right count 2^(h−1), and a=(h−1)t+t/2. Tile the binary grid by parallel pairs. The demand for fresh primes decreases, there are still ≫z right unary slots per box, and each pair support still has t distinct cofactors in its assigned dyadic interval. The additional row count relative to replacing the right digits one at a time is O((log z)³ 2^h t); this is o(F(z)). The same bounds on the maximum and reciprocal mass apply. Thus one can have overfilled indispensable boxes simultaneously in every scale triple of those ranges and keep the reciprocal sum R₀(k)+o(1) at the constructed sizes. The planted row mass still tends to zero.

The obstruction concerns the unrestricted problem because collecting the excess rows while keeping a cap close to k log k requires inexpensive cofactors near the largest primes. Carrying all removed right primes on one distinguished row to supply those cofactors is impossible in this class. A construction with several distinguished classes, or a bound on the weighted mass of interacting indispensable rows, remains to be found.

## Reproduction

[Independent finite checks](overfilled_checks.py) enumerate the actual assignments after every deletion type for t=v=2 and test the rigidity formula for every assignment attaining capacity. A separate test at t=4,v=2 checks the u≥2 period obstruction for all 26 dressed packet rows in a 30-modulus ordinary integer cover of maximum 440 and period 18,480. The four earlier binary rows lie outside the packet. The test also exhausts 632,728 pairs of local activation profiles and verifies the predicted exact hole counts on all 126 capacity-attaining profiles in the rigidity tests. The general overfilled-star classification, refinement obstruction and asymptotic constructions above are written proofs; the [Lean module](OverfilledFibre.lean) independently proves the weighted two-vector inequality, the common-line implication, and the disjoint-row line-capacity bound. All three declarations passed separate kernel replay with the standard axioms. The graph decomposition credit above is also recorded in [Shyu, Theorem 5](https://bibliotekanauki.pl/articles/32083883.pdf).
