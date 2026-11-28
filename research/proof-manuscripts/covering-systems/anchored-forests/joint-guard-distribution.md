# A common distribution on holes seen by smaller multiples of the same prime pairs

Codex (OpenAI), at Jordan Pollard's request, November 28, 2026. Written research for public review on Erdős #1189.

A row in a congruence cover tests a tuple of Chinese remainder digits. Call its tests other than one specified digit its **guard**. This note makes simultaneous use of the smaller moduli in the [separated prime ranges](earlier-multiples.md). The conclusion concerns holes of the other rows, with all the designated smaller rows set aside together.

## A finite reassignment theorem

Let the owner digits have finite alphabets of sizes q, indexed separately even if two sizes coincide. Let H be a nonempty finite set of low-coordinate patterns. In a larger constraint system with any fixed complementary rows, take H to be the projections of their uncovered points. Each movable row e at owner q can specify any one value of its low guard g_e and any one of the q owner labels. There are no other tests in that row. Assume that **every** simultaneous reassignment of the movable rows leaves a point uncovered. No independence or product assumption is made on the complementary holes.

There is a probability measure μ on H such that, with m_e(μ) the mass of the largest fibre of g_e,
```math
 \sum_q\left(\frac1q\sum_{e\in E_q}m_e(\mu)-\log q\right)_+
       \le -\sum_{y\in H}\mu(y)\log\mu(y)\le\log |H|.                 \tag{1}
```
Use natural logarithms and the convention 0 log 0 = 0. One measure works for every owner and every row at once.

**Proof.** For each row choose its guard value independently with any law π_e and choose its owner label independently and uniformly. For a fixed y and a prescribed label the probability that no row at q covers that label over y is
$\prod_e(1-\pi_e(g_e(y))/q)$. A union bound over the q labels, capped at one, bounds the probability of a surviving label by
$\exp[-(q^{-1}\sum_e\pi_e(g_e(y))-\log q)_+]$. At this fixed y the label-survival events at different owners are independent since the row pools are disjoint. An actual uncovered extension requires a surviving label at every owner. Every draw leaves some y with such an extension. Summing gives
```math
  1\le\sum_{y\in H}\exp\left[-\sum_q
               \left(q^{-1}\sum_{e\in E_q}\pi_e(g_e(y))-\log q\right)_+\right].       \tag{2}
```
For example, for any prescribed laws one simultaneous placement wipes out every low pattern for which the inner sum of positive parts exceeds log |H| + 1: the expected number of such survivors is less than one.

For the distributional claim introduce variables $0\le\lambda_q\le1$ and $x_{e,s}\ge0$ with $\sum_s x_{e,s}=\lambda_q$ for each row at q. Write
$F(y)=\sum_q(q^{-1}\sum_e x_{e,g_e(y)}-\lambda_q\log q)$.
Take $\pi_e=x_e/\lambda_q$ where defined and arbitrary laws otherwise. Each summand of F is bounded above by the corresponding positive part in (2). Thus $\sum_y e^{-F(y)}\ge1$. Normalizing these weights, or applying the finite entropy variational identity, gives
$\min_\mu(\mathbb E_\mu F-H(\mu))=-\log\sum_y e^{-F(y)}\le0$.
The two domains are compact convex polytopes. The objective is continuous, convex in μ and affine in (λ,x), so the convex minimax theorem exchanges the maximum and minimum. Maximizing at fixed μ chooses a largest fibre for each row and then selects each positive owner surplus. This proves (1). The entropy estimate and the sampling argument below are written proofs.

## Application to irreducible covers

Use the notation of [the preceding layer theorem](separated-prime-layers.md). Assume a size-k irreducible full-period set has $S-\Phi(L)\ge\epsilon\log k$ for fixed ε>0 and k sufficiently large. Fix **any** covering assignment. There is one component of net positive logarithmic surplus, one biconnected block in it, and two separated prime bins in that block with the following properties. The upper edge P of the smaller bin and lower edge Q of the larger bin satisfy $Q/P\ge k^\gamma$. Positive constants in this section depend only on ε.

* There are fixed-cofactor graphs of actual rows $pqd\le k$, for cofactors d of total reciprocal mass at least $c\log k$. Each has positive weighted expansion and minimum neighbor weight. There is also a single graph common to at least $c_0\log k$ cofactors, connected even after a polynomial number of vertex deletions. Weights of vertices are reciprocals of primes and edge weights are their products.
* On **each pair** in the union of these graphs put a disjoint list of $\lceil(q/p) k^a\rceil$ other actual moduli $pqd'$. For every retained graph row on this pair, every listed $d'<d/k^\sigma$. All listed rows have these same two largest internal primes and lie in the same block. Apart from the first digit of q their internal tests use only primes at most P.
* Set aside all listed rows together. Fix **any** new local assignments for the remaining rows of the component. Project the resulting holes onto the low digits used by the lists. From among these holes one can choose $\lfloor k^{a/12}\rfloor$ distinct projected points **in common for every graph**. After deletions described below, on every surviving edge at least a $1-k^{-a/6}$ fraction of that particular pair's earlier rows individually distinguish all the chosen points on their non-q internal tests. All the stated expansion and connectivity properties continue to hold, with decreased constants. The deleted vertices and edges and the points may depend on the complementary assignment. The lists, bins and initial graphs precede that choice.

**Reserving earlier rows.** Use the preliminary drops, group peeling and allocation proof in [earlier-multiples](earlier-multiples.md), with $a=\sqrt\delta$, where δ is that proof's small-prime exponent. In each peeled group, before filling endpoint slots take the first $\lceil(q/p)k^a\rceil$ rows in increasing modulus for each pair, or all if there are fewer. Charge these to q and continue the endpoint scan on the remaining rows. Across all groups the extra charge to one q is at most $q k^a\sum_{k^\delta<p<q}1/p+q$ since every pair is introduced in a unique group. This is $O_\epsilon(qk^a)$. The existing harmonic bound on its account, of size $qk^{2a}+O_\epsilon(qk^a)$, still holds with a changed constant. Pair lists and endpoint slots are disjoint. The earlier proof permits its initial prescribed erasures as well.

For a pair with any unassigned rows its entire pair list is full. If D is the greatest cofactor on the list, discard remaining rows of that pair with cofactor at most $D k^\sigma$. Their reciprocal cost is at most $\sigma\log k/(pq)$, by the integral bound on the harmonic sum strictly above D. All eligible primes together have reciprocal mass at most $M=2+\log(1/\delta)$ eventually. Taking σ sufficiently small costs less than the fixed remaining margin since the sum of pair weights is at most $M^2$. Apply the previous graph extraction to what remains. The bins have a positive exponent gap γ. Arbitrarily small z>0 may be used in its logarithmically common graph: its expansion is then at least $c k^{-2z}$, its minimum neighbor weight at least $c k^{-z}$. Choosing z smaller costs only a fixed factor in the number of common cofactors.

**One cut and one measure.** Use the union of pair lists for those initial graphs, before any pruning below, taking each list only once. Work in the genuine indexed component projection. By [component factorization](component-surplus.md), every placement of all its ordinary supports leaves a hole; this holds under arbitrary reassignments and applies to every fixed complement choice above. At each list row all internal prime powers with base greater than $k^\delta$ are squarefree by the preliminary drops. Its largest internal prime is q and the next is p. Thus all its internal guard coordinates other than q have base at most P, even if the integer modulus uses larger primes in earlier components. Only internal tests are being reassigned in this projection. Let H be the projection of all complementary holes onto the union of these low coordinates. For each base r the greatest exponent seen in the lists is at most $\log k/\log r$. Consequently
```math
       \log |H|\le\pi(P)\log k\ll_\epsilon P,                              \tag{3}
```
by the prime counting upper bound and $P\ge k^\delta$. Apply (1). The q for which $q^{-1}\sum_e m_e>\log q+1$ are at most $O_\epsilon(P)$ in number, of reciprocal mass $O_\epsilon(P/Q)$. Erase them. On each remaining q, writing $\bar m_{pq}$ for the mean over that pair's list, its reserved length gives
```math
                \sum_{p:pq\ \mathrm{listed}}\frac{\bar m_{pq}}p
                      \le k^{-a}(\log q+1).                                 \tag{4}
```

Draw $t=\lfloor k^{a/12}\rfloor$ points independently with law μ. For each row the chance of any collision on its guard is at most $\binom t2m_e$, since two independent draws agree on the guard with probability at most its largest atom. By (4), after weighting each pair by $1/(pq)$, the expected sum of its fractions of colliding rows is $O_\epsilon(k^{-5a/6}\log k)$. Fix a single sample attaining this bound. The pairs on which more than $k^{-a/6}$ of the rows collide have total weight $O_\epsilon(k^{-2a/3}\log k)$. Erase vertices with more than $k^{-a/6}$ reciprocal mass in such neighbors, of total weight $O_\epsilon(k^{-a/2}\log k)$ by weighted degree summation. Drop those bad pairs among the remaining vertices.

Across all graphs, a surviving vertex has lost neighbor weight at most $O_\epsilon(k^{-\gamma}+k^{-a/2}\log k)+k^{-a/6}$. For a cut take its smaller surviving side A. Its crossing weight decreases from the old cut A versus its complement by at most this bound times the weight of A. This preserves the constant expansions. Taking $2z<\min(\gamma,a/6,\delta)/2$ also preserves the polynomial expansion, positive degree and robustness to polynomially many further vertex deletions in the common graph: each further deleted vertex weighs at most $k^{-\delta}$. Both sides still have vertices because their old weights exceed the erased mass. On a surviving pair some single row separates all t sampled points, proving these projections distinct. This proves the assertions with one choice of holes across the whole family.

**Remaining obstacle.** The guard of a $pqd'$ row includes the p digit. If p is larger than t, distinct p labels alone can explain separation by many rows on that pair. Equation (4) controls the unconditioned largest atoms; it gives no corresponding bound after fixing the smaller-prime label. A route forward is to force conditional spread on the remaining guard digits or to use rows with more than one owner in a joint reassignment. No contradiction to a positive unrestricted surplus has yet been derived.

The covering principle here uses independent random placement and finite convex minimax. For related probabilistic decompositions of covers see [Bollobás, Pritchard, Rothvoß and Scott](https://doi.org/10.1137/110856332). The established logarithmic-order target has separate credit to [dk8827, Star Fleet Math and Wouter van Doorn](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9411). Öztürk gives the unrestricted upper coefficient $3/2-\log 2$. The [reproducible finite checks](joint-guard-check.py) exercise the cut independently of the asymptotic arguments.
