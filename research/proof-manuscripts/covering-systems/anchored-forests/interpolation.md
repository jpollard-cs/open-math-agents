# When local interpolation leaves a single hole

Codex (OpenAI), 27 November 2026. AI-authored research note.

Take finite alphabets $D_i$ with sizes $p_i\ge2$. A row on a nonempty support $I$ forbids one tuple of digits on $I$. Group the rows by support, with $t_I>0$ rows in group $I$. We ask when a family which leaves a hole for every assignment of these rows has a choice of assignments leaving exactly one hole. A single extra row fixing all coordinates can then give a cover. The [cyclic construction](cycles.md) demonstrates why a converse without additional hypotheses needs another idea.

## The interpolation criterion and its equality case

A sufficient condition for universal noncoverage is an allocation of nonnegative integers $l_{iI}$ with
$$
 \sum_{I\ni i}l_{iI}\le p_i-1,\qquad
 \prod_{i\in I}(1+l_{iI})\ge t_I+1 .
$$
Define a directed bipartite graph on variables and groups. Insert $i\to I$ when $l_{iI}>0$, and $I\to i$ whenever $i\in I$.

**Theorem.** Given such an allocation, an assignment with exactly one hole exists if and only if every displayed inequality is exact and the directed bipartite graph has no simple directed cycle of length at least four. When these conditions hold, every deletion of an ordinary row leaves at least two holes for every assignment of the other rows. These assertions apply to fully independent row labels, including repeated labels.

**Proof.** Identify the digits with distinct rationals in each variable. The space of polynomials on $I$ of individual degrees at most $l_{iI}$ has dimension $\prod(1+l_{iI})$. Choose a nonzero element $f_I$ vanishing on the $t_I$ forbidden tuples. The product over all groups is nonzero in the polynomial ring. It has individual degrees less than the grid sizes. Evaluation on the grid is injective for such polynomials by successive univariate interpolation. Thus some grid point is uncovered.

If just one point is uncovered, call its digits $0$. The product polynomial is a scalar multiple of the grid delta polynomial
$$
 \prod_i\prod_{u\in D_i\setminus\{0\}}(X_i-u).
$$
Indeed evaluation is injective and the two functions are nonzero at just that point. Degrees add in a product, so the vertex budgets are saturated and every factor attains its allotted degrees. Unique factorization gives disjoint sets $S_{iI}$ of nonzero digits with sizes $l_{iI}$, partitioning the $p_i-1$ values at each vertex. Up to a scalar the factor at $I$ is the product of the corresponding linear factors. Its vanishing space has dimension exactly one. Two independent members would remain independent under multiplication by the fixed other factors and under grid evaluation, yet all resulting functions would be supported on the same single point. This proves equality in the group inequalities.

For fixed $I$, extend a nonzero tuple in $\prod_{i\in I}(S_{iI}\cup\{0\})$ by zeros off $I$. Every other group's factor is nonzero on this point. No other group can forbid it. There are exactly $t_I$ such points and the group has $t_I$ rows, so their projections onto $I$ are precisely its forbidden tuples, with no repetition.

For the converse, when all budgets are tight, partition the nonzero digits accordingly and forbid exactly those tuples. A nonzero digit at $i$ chooses the group $I$ owning its value. To survive group $I$ there must then be a variable $j$ in $I$ with a nonzero digit owned by another group. Repeatedly taking witnesses gives a directed cycle of length at least four. Formally keep one outgoing arc from each nonzero variable to its owner, and at each reached group choose one outgoing arc to a witness with a different owner. This finite subgraph has no directed two-cycle. Conversely, on any simple directed cycle of length at least four choose each of its variable digits nonzero in the group to which its outgoing arc points, and all other digits zero. No group on the cycle can forbid this point because its next variable chose another group. A group off the cycle has received no nonzero digit from its own sets, so it also cannot forbid the point. This proves the stated equivalence.

After deletion in any one group its vanishing space has dimension at least two for all assignments. Multiplication and grid evaluation again preserve linear independence. Functions on at most one point have dimension at most one. Hence there are at least two holes. This completes the proof.

The grid vanishing argument is classical. For related grid polynomial methods see [Alon and Füredi](https://kam.mff.cuni.cz/~ksemweb/clanky/AlonFuredi-covering_the_cube.pdf). No priority claim is made for the general interpolation method.

## Why the cyclic example escapes

In the canonical four-cycle assignment of [cycles.md](cycles.md), after the unaries consume their digits, each edge forbids every $(u,0)$ with $u$ nonzero in the remaining alphabet. With a unique hole at zero, each such row forces the outgoing edge factor to vanish at $u$ in its source coordinate, since the factor has no root at the zero digit of its target. Thus all $p_i-1$ available linear factors at every vertex are consumed by its unaries and its outgoing edge. The chord has positive row count and no available allocation. This rules out every local product-dimension certificate for these groups, already at $d=2$.

## The sharp cap exponent for the interpolation class

Use the same count convention as the [forest theorem](anchored.pdf). Independent gadgets have disjoint prime vertices. A permanent modulus arising from a row on $I$ must be a multiple of the product of its distinct primes. The final moduli are distinct and bounded by $X$. Ordinary prime positions and one terminal closure may accompany the gadgets.

The bipartite graph of **positive** allocations is an undirected forest. An undirected cycle there could be directed consistently and would violate the theorem. A group with one positive endpoint contributes exactly its allocation. For a group with two positive endpoints $p,q$ having allocations $u,v$, the surplus over the allocated counts is $uv$ and the group has $(1+u)(1+v)-1$ rows. Root each nonempty positive-incidence component at a variable. Then $q$ can be taken as a child only once, the outgoing $u$ sum to at most $p-1$, $v\le q-1$, and $uv\le X/(pq)$. The dimension-independent dyadic bound of the two-endpoint forest proof applies verbatim. This gives total $O(X^{4/5}/\log X)$.

Each group with at least three positive endpoints has at least two child primes in this rooting. Charge its *entire* row count $t$ to the smaller $q$ of two of them. All charged primes are distinct. If $P$ is the product of all primes in its support, then $t<P$ by the group equality and the vertex budgets, and $tP\le X$ by distinctness of the actual multiples. Also $P\ge q^2$. It follows that $t\le\min(\sqrt X,X/q^2)$. Summing over primes below and above $X^{1/4}$ gives $O(X^{3/4}/\log X)$ by partial summation. Thus the sharp surplus over $F(\sqrt X)$ remains $\Theta(X^{4/5}/\log X)$ even in this larger class. The lower construction is the explicit forest, whose allocations satisfy the equalities and cycle criterion. A support can have primes with zero allocation, and they are included in $P$ throughout.

For reciprocity pool all groups with one positive endpoint at that endpoint. If other groups spend $l$ units at $p$, this costs at least $l/p^2$ from its ideal unary mass. For any group with two or more positive endpoints choose two of them, with allocations $u,v\ge1$. Put $n=(1+u)(1+v)$ and $D=\prod_{i\ne p,q}(1+l_{iI})$. The group mass is at most $H_{nD-1}/P\le H_{n-1}/(pq)$. Indeed the extra $D-1$ blocks of $n$ harmonic terms contribute at most one each, $H_{n-1}\ge1$, and $P\ge pqD$. The two chosen endpoint allowances are $u/p^2+v/q^2\ge 2\sqrt{uv}/(pq)$ whereas $H_{n-1}\le(11/6)\sqrt{uv}$ as in the forest proof. Summing yields the same sharp penalty of one eleventh of the mass in multi-endpoint groups. The digit budget is at most the ordinary row count because every group contributes at least its allocation sum. The same first-position knapsack and higher-position tail therefore bound the reciprocal sum by $R_0(k)+o(1)$ across this class. The unrestricted additive gain in [cycles.md](cycles.md) exceeds this ceiling.

## Converse for tree supports

When the actual ordinary supports on the new coordinates are singletons and the edges of a forest, and some assignment leaves just one hole while no assignment covers, such an allocation necessarily exists. Root each tree. In a subtree write $a_x$ for the minimum possible number of feasible digits at its root $x$ over all assignments of that subtree. A child subtree with minimum zero would cover the entire grid by itself and is impossible. If $U_x$ is the number of unary rows and $t_{xy}$ the number on each child edge, then exactly
$$
 a_x=\max\left(0,p_x-U_x-\sum_y\lfloor t_{xy}/a_y\rfloor\right).
$$
The lower bound counts the rows needed to eliminate a parent label through each child. For equality choose minimizing child assignments independently, distribute distinct unwanted parent values to the unary and child groups to capacity, and on each child group prohibit all its feasible labels at each assigned parent value. Any leftover rows can repeat cells or be chosen arbitrarily. This proves the recurrence.

In a one-hole assignment each component root has exactly one feasible digit with a unique continuation, attaining $a_x=1$. More generally, at a node whose actual feasible count equals $a_x$ and which has a unique continuation at a marked feasible digit, all counting capacities must be attained, since $a_x>0$. Write $v=\lfloor t_{xy}/a_y\rfloor$, and let $m_y\ge a_y$ be the actual feasible count at the child. Eliminating $v$ parent values and leaving a unique continuation at the marked parent costs at least $(v+1)m_y-1$. Since $t_{xy}<(v+1)a_y$, we have $m_y=a_y$ and $t_{xy}=(v+1)a_y-1$. The remaining child digit has a unique continuation, so induction applies throughout. Put $l_{x,xy}=v$ and $l_{y,xy}=a_y-1$, and give the unary group its full count. These allocations have the required equalities. Values $v=0$ are allowed. The converse follows directly from the interpolation theorem because the incidence structure for these supports has no undirected cycle. This classifies tree-support single holes with unaries and arbitrarily many rows per edge.
