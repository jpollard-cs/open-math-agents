# Cycles sharing a prime coordinate

Codex (OpenAI), 27 November 2026. Written supplement to [the cyclic construction](cycles.md).

The sharp surplus in the number of congruences from cyclic blocks joined at single prime coordinates is $\Theta(X^{3/4}/\log X)$ at cap $X$, over the ordinary baseline $F(\sqrt X)=\sum_{p\le\sqrt X}(p-1)$. This holds also as the order of the surplus in the initial interval of attainable sizes. Their unrestricted-depth reciprocal improvement over the ordinary baseline stays bounded. It can be strictly positive by the explicit cyclic examples.

## Gluing at an articulation

Use a finite collection of the two-path blocks of [cycles.md](cycles.md), with one chord per block. Arrange them in a rooted incidence tree of blocks and variables. Each new block meets earlier blocks at only one variable, called its root within that block. The other variables are new and may support other blocks later. Each block has an integer $s=d-1\ge1$. Give each ordinary cycle edge $s$ rows and its chord $s^2$ rows. At a vertex $p$ take $p-1-\sum_{B\ni p}s_B$ unary rows, requiring the expression nonnegative. Use one distinguished singleton on the whole connected component. Blocks share only vertices and use distinct prime coordinates otherwise.

For arbitrary reassignment, an incident child block, once the subtrees beyond it have been processed, precludes at most $s$ values at its root. To see this, take any $s+1$ root values and any $s+1$ feasible digits at each new vertex inside the block. Those feasible digits can be selected because the unary and lower-block counts leave at least $s+1$ at each such vertex. Internal coherence across the different child subtrees follows from disjointness. The two-path argument leaves a surviving tuple. Thus at the top variable at least one label survives.

Suppose the top has one surviving tuple. All quotas for disjoint blocked labels and unary rows must be attained. In a child block take its $s$ blocked root values together with the value of the unique extension, and any $s+1$ internally feasible digits at each child vertex, including its uniquely used value if possible. If a child had $s+2$ feasible digits, choose a subset omitting that value and obtain another extension. Each child therefore has exactly $s+1$ feasible digits and has unique continuation at the used value. Any missing edge or chord row gives two internal tuples on these alphabets, by the deletion lemma. Both tuples must use the same unblocked root value and each extends to the subtrees; this contradicts uniqueness. The argument propagates down the tree and forces every row.

Conversely, assign disjoint sets of $s$ unwanted labels at a root to its child blocks and reserve zero. A vertex attached from above reserves a set of $s_{\rm parent}+1$ feasible labels including zero. Use its remaining labels for its unary rows and child-block quotas. On the chosen $s+1$ labels of every participating vertex, implement the directed cycle and chord with zero marked. At a block root the chosen labels are zero and the blocked group for this child. Every blocked label has no continuation, and zero has exactly one. A root label outside the chosen set has some continuation, since treating zero as a feasible root label and replacing it by the outside label cannot activate any row involving that root. Thus the intended feasible sets are attained and the global hole is unique. The ordinary deletion argument applies after all residues are reassigned. Distinct integer moduli can be obtained by the fixed-period dressings described in [cycles.md](cycles.md).

## Sharp cap order

The surplus is $\sum_B s_B^2$. Indeed each incidence consumes $s_B$ unary rows and each cycle edge creates $s_B$ rows, balancing on each cycle. Only its chord yields an excess.

If neither chord endpoint is the block root, charge to its smaller terminal prime $q$. It was introduced by that block. Its total charge over such blocks is $O(X^{3/4}/\log X)$ by the disjoint-terminal argument. In the remaining blocks let $p$ be the root and $q$ the other terminal. The latter occurs at most once as a new terminal. The root may occur arbitrarily often. We have
$$
 \sum_{B:\,\mathrm{root}=p}s_B\le p,\qquad s_B\le q,\qquad s_B^2pq\le X .
$$
Put $Y=X^{1/4}$. Roots $p\le Y$ contribute at most $\sum_{p\le Y}p^2\ll Y^3/\log X$. For the remaining blocks the child primes $q\le Y$ likewise contribute at most this amount. Dyadically group the remaining primes in $[P,2P),[Q,2Q)$ with $P,Q\ge Y$. Prime counts and the distinctness of $q$ bound each bin, up to an absolute factor, by
$$
 \frac1{\log X}\min\left(\frac{X}{P},\ P^2\sqrt{\frac{X}{PQ}}\right).
$$
The first estimate sums the individual chord bounds over child primes. The second sums $s_B$ at each parent and bounds the other factor $s_B$ individually. For fixed $P\ge Y$ the second term drops below the first at $Q=P^5/X$. There are $O(1+\log(P/Y))$ dyadic bins before that transition and a geometrically decreasing tail. Summing $X(1+\log(P/Y))/P$ over dyadic $P\ge Y$ costs $O(X^{3/4})$. Prime positions of higher exponent contribute $O(X^{2/3}\log X)$ as in the forest theorem. This proves the upper estimate.

For attainability take a large terminal prime $z$ and cap $X_z=z(z+1)$. Choose a fixed narrow band of primes between $1.01\sqrt z$ and $1.1\sqrt z$, and partition all but at most three into disjoint quartets. There are $J\asymp\sqrt z/\log z$ such groups, whose total reciprocal prime mass tends to zero. Set $B=\lfloor\sqrt z/10\rfloor$. Choose $0\le s\le B$ independently on each quartet, with $s=0$ representing independent unary groups and a singleton. Before those substitutions, prepare the nondesignated primes through $z/10$ with positions up to $z+1$ as in [the forest construction](anchored.pdf). At each such prime $r$ use the available $d<r$ and fill through $2r$ when needed. Prime powers up to $2r$ are affordable, and the fraction of unavailable integers in this range is $o(1)$ uniformly after the first designated prime, by the same divisor count. Each quartet support group with $t$ rows uses different dressings up to $2t$, excluding multiples of designated primes. All remaining dressings divide the prepared period, and at least $t$ survive. Unary and cycle-edge groups easily fit. For chords the cap follows from $2B^2(1.1\sqrt z)^2<X_z$. No designated square is at most $z+1$ eventually. Finish by the ordinary prime positions and the terminal $z$ closure. All numerical moduli in different quartet groups are distinguished by their designated supports.

The baseline $L(z)$ in the forest paper now receives an arbitrary sum of $J$ squares $s_i^2$ with $0\le s_i\le B$. Every integer through $(J-4)B^2$ occurs. Use as many full squares as possible, then write the remainder below $B^2$ as four squares by Lagrange's theorem. Consecutive baseline gaps are $O(z\log z)$, so the attained intervals overlap and supply the claimed initial interval. As in the forest paper $z$ can be taken as the last prime with $z(z+1)\le X$, losing only $O(\sqrt X)$ in $F(\sqrt X)$. All smaller fixed sizes already fit using the ordinary constructions.

## Bounded reciprocal gain

Sum the allowances of $s/p^2$ from each incidence at each vertex. They can be used independently because its actual unary deficit is the sum of its incidence allocations. By the cycle estimate these allowances absorb all path-edge mass and, when $s\ge4$, the chord mass as well. For $s\le3$ the residual at a chord is at most $H_9/(pq)$. When neither terminal was already present, sum this by $2/(pq)\le1/p^2+1/q^2$. Otherwise group the chords by their repeated parents $p$ and new terminals $q$. Each $p$ occurs at most $p$ times and each $q$ once. Hölder gives, over all those incidences,
$$
 \sum_{B}\frac1{p_Bq_B}
 \le \left(\sum_Bp_B^{-3}\right)^{1/3}
      \left(\sum_Bq_B^{-3/2}\right)^{2/3}
 \le \left(\sum_p p^{-2}\right)^{1/3}
      \left(\sum_q q^{-3/2}\right)^{2/3}<\infty .
$$
This bound is uniform in depth, branching, prime sizes and number of blocks. The ordinary higher positions obey their harmonic bounds and the singleton or terminal closing row contributes $o(1)$. Together with [the transfer principle](transfer.md), the reciprocal optimum for this full-period class has a finite positive limiting excess over $R_0(k)$. No estimate here bounds the sum over many blocks that share two variables in different configurations.
