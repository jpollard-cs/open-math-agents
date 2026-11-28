# The sharp uniform ratio for successive maximal matchings

For a finite simple graph with at least one edge, choose a maximal matching, delete its edges, and repeat for a total of $b$ rounds. Write $S$ for the union of the chosen matchings and $O$ for a largest subset of edges with maximum degree at most $b$. Define $r_b$ as the infimum of $|S|/|O|$ over graphs and all legal choices of the matchings.

**Theorem.** The largest constant $c$ for which $|S|\ge c|O|$ in every graph and for every $b\ge1$ is
$$
\inf_{b\ge1}r_b=\lim_{b\to\infty}r_b=2\sqrt3-3=0.4641016151\ldots.
$$
Finite simple bipartite graphs suffice to approach this value. Their optimal comparison subgraph is spanning and $b$-regular, so it too can be scheduled in $b$ rounds. The proof gives explicit finite-budget bounds. For example, $r_3\le13/27<1/2$.

Jesper W. Mikkelsen posed the graph question in 2013. For the equivalent First-Fit routing of arriving edges to colors, Favrholdt and Nielsen established the lower constant for every fair algorithm and attained it asymptotically for Next-Fit. The construction below attains the same limit for First-Fit. The two algorithms have strictly different worst ratios at every fixed $b\ge3$.

## The lower bound

We retain the integer degrees in the charging argument of Favrholdt and Nielsen. Define
$$
 f(x)=\frac{1-x+x^2}{2-x},\qquad F_b=\min_{a=0,\ldots,b} f(a/b).
$$
In each round, at least one endpoint of every omitted comparison edge is matched, since otherwise the edge could have been added. The matched endpoint may change from round to round. Thus the endpoint sets of round labels of such an edge cover all $b$ labels. This uses only maximality, and holds for an arbitrary simple graph and degree-$b$ comparison.

At each vertex denote its selected degree by $s$, its degree in $S\cap O$ by $d$, and its degree in $O\setminus S$ by $u$. Give the vertex a budget $(s-cd)/2$, where $c=F_b\le1/2$, and distribute it evenly over its $u$ omitted comparison edges if $u>0$. The total budget is $|S|-c|S\cap O|$. To obtain $|S|\ge c|O|$, it suffices to show each omitted edge receives at least $c$.

At an endpoint of such an edge $u\le b-d$. Write $x=s/b$ and $z=d/b$. Double its contribution is at least $(x-cz)/(1-z)$. Its minimum over allowed $z\in[0,x]$ is bounded below by the increasing function
$$
 h(x)=\begin{cases}(1-c)x/(1-x),&x<c,\\ x,&x\ge c.\end{cases}
$$
This follows by differentiating in $z$. The condition $u>0$ excludes $z=1$. The two values of $x$ sum to at least one, so it suffices to check $h(x)+h(1-x)\ge2c$ at the grid points. If both arguments are at least $c$, the sum is one. Otherwise interchange endpoints to arrange $x<c$. The inequality then reduces to $f(x)\ge c$. This proves $r_b\ge F_b$. Now $f(x)=(2-x)-3+3/(2-x)$ has its unique minimum $2\sqrt3-3$ at $x_*=2-\sqrt3$.

## A finite graph realizing the limiting upper bound

Choose $d\ge2$ and $m=2d-1<b$. Set $q=b-d$. The first $m$ rounds are the early rounds. Use all $d$-element subsets $s$ of $[m]$ as labels. On each shore of a bipartite graph put $b$ low vertices and $q$ high vertices per label. A low vertex is matched exactly in the early rounds belonging to its label. A high vertex is matched in those early rounds and in all late rounds.

For $i\in s$ put $T_i(s)=([m]\setminus s)\cup\{i\}$. It is a $d$-set. The map $T_i$ permutes the labels containing $i$ and is its own inverse. Also fix a permutation $P$ of all labels for which $s\cup P(s)=[m]$. Such a permutation exists by Hall's theorem: join $s$ on the left to the $d$ labels $T_i(s)$ on the right. The resulting bipartite graph is $d$-regular on both shores, so it has a perfect matching.

* In early round $i$, pair each active left vertex with the right vertex of the same kind and copy index at label $T_i(s)$.
* In late round $m+j$, $1\le j\le b-m$, pair each left high vertex $(s,a)$ with the right high vertex $(P(s),a+j\bmod q)$.
* Add unused comparison edges from every low vertex of label $s$ on the left to all $q$ high vertices of label $P(s)$ on the right. Also join each high vertex at $s$ on the left to all $b$ low vertices at $P(s)$ on the right. Include all early low-to-low edges in the comparison set.

All prescribed rounds are matchings. The early opponents $T_i(s)$ are distinct as $i$ varies. The late cyclic shifts are distinct and nonzero since $b-m=q-d+1<q$. Thus the graph is simple. Every edge still available in round $i$ has at least one matched endpoint: early selected edges have endpoint labels covering the early rounds, late selected edges additionally have two high endpoints, and unused edges have a high endpoint and early labels covering $[m]$. In a late round every remaining edge has a high endpoint, since all low-to-low edges were selected in the early rounds. This checks maximality against *all* remaining edges.

Every vertex has comparison degree $b$, so the comparison is optimal, including against non-colorable degree-bounded comparators. With $D=\binom md$, the count per left shore gives
$$
 |S|=D[bd+q(q+1)],\qquad |O|=Db(b+q).
$$
Indeed a high vertex has greedy degree $d+(b-m)=q+1$. Therefore
$$
 r_b\le f(d/b)+\frac{b-d}{b(2b-d)} .
$$
For all large $b$, take $d$ nearest $b(2-\sqrt3)$. The right side tends to $2\sqrt3-3$ and differs from it by $O(1/b)$. This and the lower bound prove the main theorem.

**Size of witnesses.** The construction can also approach the constant with only $b$ times an arbitrarily slowly growing factor in the number of vertices. Given any function $g(b)\to\infty$, choose an auxiliary budget $k\to\infty$ so slowly that $2^k\le g(b)$ and $k\le\sqrt b$. Build the construction above at $k$, then replace each vertex by $t=\lfloor b/k\rfloor$ clones and each edge by a complete bipartite graph between the two clone sets. Replace each original round by $t$ consecutive rounds, using the cyclic perfect matchings between each selected pair of clone sets. Blocking persists within the block because every clone of an active vertex is matched in each subround. Extend the resulting $tk$ rounds maximally to $b$. The comparison count scales by $t^2$ and the comparison degree is $tk$. If the original graph had $V$ vertices on each shore the additional selections number at most $(b-tk)tV$, against $t^2kV$ comparison edges. Thus the extra ratio is at most $k/(b-k)=o(1)$. Each shore has at most $2tk\,2^k=O(bg(b))$ vertices.

**First-Fit equivalence.** Present the selected edges round by round and then the unused edges. In each round every earlier color is blocked at some endpoint, and the designated color is free. Conversely the color classes of any First-Fit arrival sequence are successive maximal matchings: any later or rejected edge found each earlier color blocked when it arrived. A $b$-edge-colorable comparator always has maximum degree at most $b$. For the reverse comparison of worst ratios, replace an arbitrary graph by its bipartite double cover, lifting an edge in both orientations between opposite shores and lifting every round in full. Both endpoint copies are matched whenever the original vertex was matched. Every round stays maximal, the counts double, and the lifted comparison set is $b$-edge-colorable by König's theorem. Disjoint copies eliminate any additive constant in the competitive-ratio convention.

## A sharper upper estimate at finite budgets

For $0\le m<b$ put $x=m/(2b)$, let $K$ be binomial with parameters $m,1/2$, and define $A=\mathbb E[b/(b-K)]$. A second family of finite simple bipartite graphs gives
$$
             r_b\le \frac{A-x}{A+1}.
$$
Use all subsets of $[m]$. On each shore give high label $s$ vertex mass one and low label $s$ mass $w_s=b/(b-|s|)$. A low vertex is active precisely at the elements of its label. A high vertex is active at those elements and in all late rounds. In early round $i$, match high vertices of label $s$ with high vertices at $([m]\setminus s)\cup\{i\}$, an involution on the labels containing $i$. For each late round match high vertices at complementary labels. For unused comparison edges pair low $s$ with high $\bar s$ in both orientations. The required masses agree because $(b-|s|)w_s=b$. Low selected edges alone are also in the comparison.

It remains to pair the early low ports. For fixed $i$, set the pairing mass from $s$ to $t$ to zero unless both contain $i$ and their union is $[m]$. For the allowed pairs use
$$
 b\int_0^1 z^{b-m-1+|s\triangle t|}(1-z)^{|s\cap t|-1}\,dz .
$$
These masses are symmetric and rational by the integer beta integral. For each bit other than $i$, the local factors for $(0,1),(1,0),(1,1)$ are respectively $z,z,1-z$. Summing over the partner leaves factor $z$ at each zero bit of $s$ and factor one at each one bit. The row sum is $b\int_0^1 z^{b-|s|-1}\,dz=w_s$, as required. Both margins therefore agree with the active vertex masses.

Clear all denominators. At each label, assign the requests for each active round bijectively to the vertices there. Give each low vertex $b-|s|$ unused comparison ports, and each high vertex $b$ such ports. The aggregates match for each complementary pair. This gives a bipartite multigraph. To make it simple, if the largest multiplicity is $J$, replace every vertex by $J$ copies indexed modulo $J$. Lift parallel edges between a fixed pair with distinct cyclic offsets. Degrees, blocking labels and the ratio are preserved. Every comparison degree is exactly $b$.

Per $2^m$ labels the selected count on the left is $b(A-1)+b-m/2$, using $|s|w_s=b(w_s-1)$. The comparison count is $b(A+1)$. This proves the bound. For $b=3$ and $m=1$ it gives $A=5/4$ and $r_3\le13/27$. With $m$ nearest $2b(2-\sqrt3)$, expansion gives
$$
 r_b\le 2\sqrt3-3+
 \frac{1/\sqrt3-1/2}{b}+O(b^{-2}).
$$
Indeed Taylor-expand $g(y)=1/(1-y)$ at $x$ for $y=K/b$. In the pertinent range $m/b$ stays uniformly below one. The centered third moment vanishes, and the centered fourth moment of $K$ is $O(m^2)$ by independence. Thus $A=(1-x)^{-1}+x/[2b(1-x)^3]+O(b^{-2})$. The derivative of $(A-x)/(A+1)$ with respect to $A$ is $(1+x)/(A+1)^2$. The coefficient at $x_*$ is $x_*(1+x_*)/[2(1-x_*)(2-x_*)^2]=1/\sqrt3-1/2$. Rounding $m$ affects $f(x)$ only at second order since $f'(x_*)=0$. This gives a one-sided estimate of the finite-budget correction.

## First-Fit strictly beats Next-Fit for each fixed budget of at least three

The construction in Favrholdt–Nielsen, Theorem 4.1, gives Next-Fit upper bounds $f(a/b)$ at integer $a$ (their parameter is $b-a$). Combining with the integer charging bound gives its exact ratio $F_b$. We show $r_b>F_b$ for $b\ge3$. The argument needs attainment at each fixed budget. Here is the finite linear-program argument in brief.

Normalize selected edge mass to one. Variables count vertices per activity mask, and edges per pair of masks, selection round (or unused), and comparison bit. Discard edges in neither set and isolated vertices. Edge types must obey activity and earlier-round blocking. At each label the endpoint mass for each active round equals the vertex mass. Comparison endpoints have mass at most $b$ times the vertex mass. Maximize comparison mass. This rational program has a finite optimum by the charging lower bound, which uses only these local inequalities and sums and applies to rational feasible points after realization as follows. Clear denominators, make the indicated vertices on each shore and place each unordered edge type in both orientations (twice for equal labels). Assign selected ports bijectively per round. Distribute unused comparison ports over the vertices' remaining slots. All selected comparison degrees are at most $b$ at every vertex before distributing, and the aggregate capacity bound guarantees room. Lift to a simple graph by cyclic offsets as above. Rational linear programming now gives a rational optimizer and an actual graph attaining $r_b$. Conversely every schedule supplies a feasible point. This attainment argument is sufficient for the strict comparison below.

Suppose equality occurs at $c=F_b<1/2$. Every omitted comparison edge must receive exactly $c$ and every vertex budget must be spent. Its endpoint degrees must add to exactly $b$ by strict monotonicity of $h$. One endpoint is low, with $s/b<c$, $d=s$ and $u=b-s$. Its selected degree $K=s$ minimizes $f(K/b)$. The other endpoint is high, with $d=0$ and $u=b$. The sets of rounds in which the two endpoints are matched, their activity masks, are complementary. These assertions follow from equality in each charging inequality. For $b\ge3$ the minimizing grid points are interior and positive ($f(1/b)<1/2$), so the endpoint budget is positive and $u=b-d$ is necessary. Vertices with no omitted edge have zero budget and hence no selected edges. We can discard them. Consequently every selected edge joins two low vertices or two high vertices. Mixed edges cannot be selected because precisely the low vertices have all their selected edges in the comparison.

Choose a uniformly random low vertex and let its activity indicators be $I_i$, with $K=\sum I_i$, $\mu=\mathbb E K$ and $p_i=\mathbb E I_i$. A uniformly random high vertex has mask distributed as the complement of this low mask **biased by $b-K$**. This follows by counting the omitted edges from both ends. The minimum of $f$ on the grid is attained at one integer or two consecutive integers because it decreases and then increases. Let $k_{\max}$ denote the largest minimizing integer. A low edge selected in round $i$ must have endpoints jointly active in every earlier round and both active at $i$. Hence $i\le2k_{\max}-1$. For $b\ge16$ we have $k_{\max}\le bx_*+1\le b/3$. For $3\le b<16$ direct evaluation of the grid gives the unique minimizers, in order, $1,1,1,2,2,2,2,3,3,3,3,4,4$. In particular the low vertices are all idle in round $b$, and their complementary high masks are all active then.

Pairing all high vertices in round $b$ forces at most half of those vertices to be inactive in any given earlier round. In low variables this means
$$
 \frac{\mathbb E[(b-K)I_i]}{b-\mu}\le\frac12 .
$$
It also holds at $i=b$ because $p_b=0$. Thus $p_i\le M=1/2+1/[4(b-\mu)]$: the covariance of $K$ and $I_i$ is at most $1/4$ since $K$ takes at most two consecutive values. When $K$ is constant take $M=1/2$.

Every round-$i$ low matching pairs all its active low vertices, with at least one endpoint active at each $j<i$. It follows that $2\mathbb E[I_i I_j]\ge p_i$. Summing gives $\mathbb E[K(K-1)]\ge\sum_i(i-1)p_i$. Subject to $p_i\le M$ and $\sum p_i=\mu$, the sum on the right is minimized by filling the earliest indices first. If $\mu/M=l+\theta$ with $l$ integral and $0\le\theta<1$, its minimum is $M[l(l-1)/2+l\theta]\ge\mu^2/(2M)-\mu/2$. Therefore
$$
 \operatorname{Var}K\ \ge\ \frac{\mu}{2}-\mu^2\left(1-\frac1{2M}\right).
$$
A constant $K$ is impossible, since then $M=1/2$ and $\mu>0$. This handles all the smaller budgets as well. For $b\ge16$, $bx_*-1\le\mu\le b/3$. Inserting the stated $M$ gives $\operatorname{Var}K\ge\mu/2-\mu^2/[2(b-\mu)+1]\ge\mu/4>1/4$. But support on two consecutive integers gives variance at most $1/4$. This contradiction proves strictness.

## Scope and sources

The theorem determines the optimal constant uniform in $b$ and the limit of the fixed-budget ratios. The finite-budget estimates in this note give inequalities. The first-order asymptotic of $r_b-(2\sqrt3-3)$ remains undetermined here. The repository's separate fixed-budget Lean statement specifies an exact dual linear program. Its formal proof remains a separate task. The proof of the uniform constant above is self-contained and uses neither that statement nor a numerical solver.

- Jesper W. Mikkelsen, “Size of $b$-matching constructed from $b$ maximal matchings,” MathOverflow (2013). [Original question](https://mathoverflow.net/questions/148821/size-of-b-matching-constructed-from-b-maximal-matchings)
- Lene Monrad Favrholdt and Morten Nyhave Nielsen, “On-Line Edge-Coloring with a Fixed Number of Colors,” *Algorithmica* **35** (2003), 176–191. [Journal article](https://doi.org/10.1007/s00453-002-0992-3) · [Conference version, Theorems 3.2, 4.1 and 5.1](https://ndl.ethernet.edu.et/bitstream/123456789/50431/1/Sanjiv%20Kapoor_2000.pdf)
- The fixed-budget formalization is tracked separately. [Statement PR 759](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/759)
