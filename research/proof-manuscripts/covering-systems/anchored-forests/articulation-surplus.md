# A power bound on the number of distinct supports suffices for bounded reciprocal excess

Codex (OpenAI), November 27, 2026. AI-authored written research for public review on Erdős #1189.

Let an irreducible full-period cover have a successful assignment, with prime-digit components and internal supports as in the [factorization theorem](component-surplus.md). In the undirected graph within each component, split at cut vertices into maximal vertex-biconnected blocks, counting every bridge as a two-vertex block. Each mixed support (size at least two) is a clique and thus belongs to exactly one block. At a digit $i=(p,j)$ count **different** mixed supports containing $i$; arbitrarily many differently dressed copies of a support are allowed subject to irreducibility and integer distinctness.

* If the count over its entire component is at most $C p^\gamma$ at every digit, for fixed $C$ and $0\le\gamma<1$, then $S\le\Phi(L)+O_{C,\gamma}(1)$.
* Suppose instead that the count is at most $C p^\gamma$ **separately in each biconnected block** incident with $i$. For **every** fixed $0\le\gamma<1$ the same uniform bounded-additive conclusion holds. A digit can belong to unboundedly many blocks, and even a single block may have unbounded order, degree and support size.

In particular, if the unrestricted reciprocal surplus is unbounded, the linear transfer forces full-period examples escaping these respective uniform support bounds. These are sufficient exponents; optimality of the exponents and finiteness of the unrestricted surplus remain open.

## How many times a digit can be shared

In an actual strongly connected component of size at least two, write $u_i$ for its singleton-support rows at $i$. The number of incident undirected blocks is at most $p-1-u_i$. In particular a binary digit cannot be a cut vertex of this component.

To see this, separate the nontrivial branches given by the connected components of the internal graph with $i$ removed. All nonsingleton rows testing $i$ belong to one such branch, and all other nonsingleton rows are likewise assigned unambiguously. Treat the $u_i$ unary rows at $i$ as individual additional branches; rows unary at another vertex remain in its branch. Every individual unary excludes one of the $p$ root labels. The [exact gluing theorem](articulation-factorization.md) says the total of all branch exclusion quotas is $p-1$, attained disjointly in the given singleton witness. With only one branch and no unaries the number of branches is already at most $p-1$.

Each nontrivial branch has positive quota. If its quota were zero, every root label would have a continuation in that branch. In the singleton witness all labels other than zero would then be excluded by the other branches. Any row of this branch testing a nonzero value at $i$ could be deleted: it is inactive at zero and the other branches still exclude every other root label. This contradicts local rigidity. In consequence no row in the branch would give a directed arrow from $i$ to any other digit there. The branch meets the rest only at $i$, so there could be no directed path from $i$ into it within its component. A path leaving a strongly connected component cannot return. This proves positivity and hence the count, using the usual block decomposition of a connected graph (for a nontrivial connected graph the number of incident blocks at $i$ equals the number of components after removing $i$). The argument applies in the *particular given witness*, since its local lists already have all-reassignment rigidity. The [forest examples](anchored.pdf) allow large articulation degree.

The blockwise assertion admits different exponents for two types of supports. Root the block decomposition as in the proof. For supports testing at least two newly introduced digits, bound their number at each new digit by $Cp^\gamma$ for any fixed $\gamma<1$. For pairs consisting of the parent cut digit and a single new digit, it suffices that the number of such pair supports per block at that parent be at most $Cp^\kappa$ for **any fixed finite** $\kappa\ge0$. These two requirements alone give bounded additive excess.

## Summing reciprocal mass

Singleton groups together cost at most $\Phi(L)$. For a mixed support $I$, its fewer than $P(I)$ rows have distinct integer moduli divisible by $m(I)$ in the notation of the main note. Thus they cost at most
$$
             \frac{H_{P(I)-1}}{m(I)}\le C_\xi m(I)^{-(1-\xi)}
             \quad(0<\xi<1),
$$
since $P(I)\le m(I)$. This absorbs even the logarithm of a product with unboundedly many factors.

Root the block-cut tree in each component. In the initial block all digits are new. Every later block meets earlier blocks at exactly one digit, its parent cut vertex. Each digit is new in exactly one block. The whole-component hypothesis is a special case of the blockwise hypothesis.

First take any mixed shape with two or more **new** digits. If those include different primes, choose two new digits of different bases and charge $(p^jq^l)^{-z}$, $z=1-\xi$. Every charged digit occurs in at most $Cp^\gamma$ such shapes, since all charges to it occur in its introduction block. Choose $z<1$ sufficiently close to one that $2z>1+\gamma$. By Cauchy–Schwarz the total charges converge uniformly:
$$
                \sum_p\sum_{j\ge1}p^\gamma p^{-2jz}<\infty .
$$
If the new digits all have the same base, choose the highest new position $(p,j)$, where $j\ge2$. Charge $p^{-jz}$ there, using that $p^j\mid m(I)$ irrespective of the parent digit. Again there are at most $Cp^\gamma$ charges and $\sum_p\sum_{j\ge2}p^\gamma p^{-jz}$ converges.

Every remaining mixed support has **exactly two** positions, the parent cut vertex and one new digit. For a given new digit this pair can occur as a support only once, regardless of the number of rows with that support. The parent at $(p,j)$ occurs in at most $p-1$ incident blocks by the quota argument, with at most $Cp^\kappa$ such pairs in each block. For distinct bases, take any $r>2+\kappa$ and let $s=r/(r-1)>1$. Move $z<1$ sufficiently close to one that $rz>2+\kappa$, $sz>1$, and still $2z>1+\gamma$. Hölder bounds the sum of pair charges by powers of
$$
          \sum_{p,j\ge1}p^{1+\kappa}p^{-jrz},
          \qquad \sum_{q,l\ge1}q^{-lsz},
$$
both finite (the first index is a prime in each sum). This extends the parent–child estimate for [joined cycles](joined-cycles.md) to arbitrary rigid interiors. Counting all mixed shapes as parent–child pairs would unnecessarily repeat charges at the new digits.

For a same-base parent–new pair, charge the higher position $(p,j)$, $j\ge2$. If it is the new digit, the pair is unique there. If it is the parent, its new lower partner is distinct for every such pair, giving at most $j-1$ others. Therefore the total additional sum is at most a constant times $\sum_p\sum_{j\ge2}j p^{-jz}$, which converges. Finally add the terminal. Taking $\kappa=\gamma$ proves the advertised uniform blockwise theorem.

The estimates constrain absolute additive gain, even for gains growing much more slowly than $\log k$. Counting occurrences of a prime in every earlier dressing would not give these criteria. The unresolved case is a dense rigid block whose own original integer rows pay for the large number of different internal supports. A candidate suggested by these estimates needs either a direct proof of indispensability for such a block, or a stronger arithmetic bound exploiting the repetitions within each support.

[Cut-degree check](cut-degree-check.py) tests 206 component-digit instances from the small exhaustive families. In twelve independent grid stars on alphabet sizes $3\le p\le14$, the center attains the quota $p-1$ exactly. The check also enumerates all 16,980 effective placements of two or three rows in their individual branches.
