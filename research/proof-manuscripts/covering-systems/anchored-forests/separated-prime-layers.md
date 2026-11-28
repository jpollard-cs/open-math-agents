# A fixed cofactor on a robust graph of separated prime factors

Codex (OpenAI), at Jordan Pollard's request. AI-authored written research for public review on Erdős #1189.

Let an irreducible set of $k$ distinct moduli contain its period $L$. Put $S=\sum 1/n$ and $\Phi(L)=\sum_{p^j\mid L,\,j\ge1} H_{p-1}/p^j$. The original irreducibility condition allows all residues to change after any deletion. The [transfer theorem](normalised-surplus.md) identifies a positive upper limiting gain over $1/2$ with the existence of sets of this kind with $S-\Phi(L)\ge\epsilon\log k$ for some fixed $\epsilon>0$ and unbounded $k$.

**Theorem.** Assume this inequality, and take any successful assignment at sufficiently large $k$. In one strongly connected digit component with net surplus at least $\nu\log k$, there is one vertex-biconnected block, a pair of disjoint intervals of primes and a set $T\subset[k^\beta,k]$ of integers such that
$$
                       \sum_{d\in T}1/d\ge c\log k.
$$
Here and below positive constants can depend on $\epsilon$. Primes $p$ in the first interval and $q$ in the second satisfy $p\ge k^\delta$ and $q\ge p^{1+\theta}$. For **each fixed** $d\in T$ there is a bipartite graph across those intervals whose every edge gives a different actual row $pqd\le k$ of the specified component, with both prime digits internal. Its whole internal support lies in the specified block. No row is used for two different triples. The graph can vary with $d$.

Give a vertex $v$ weight $w_v=1/v$, a set weight $w(A)=\sum_{v\in A}w_v$ and an edge weight $w_uw_v$. Both sides have weight at least $c$. Every vertex has neighbor weight at least $c$. Every bipartition $A,B$ of its vertices satisfies
$$
              e(A,B)\ge c\min(w(A),w(B)).
$$
Deleting any set of vertices of reciprocal mass at most $c/4$ from this **same graph** preserves the inequality with $c/2$ and preserves positive weighted minimum degree. Constants may be decreased throughout. More generally, for any fixed integer $r\ge1$, one such graph works for all $r$ distinct cofactors in a tuple simultaneously, for tuples of total product weight $\gg_{\epsilon,r}(\log k)^r$. The graph and its constants can now depend on $r$ (the constants are uniform over the selected tuples). The one block and the intervals still work for them all. There is also a tuple of at least $c_0\log k$ distinct cofactors with a common graph that stays connected after any $k^{c_1}$ vertices are deleted. Each of its smaller primes $p$ still has at least $p^{1+\theta/2}$ larger neighbors, before shrinking the exponent again if needed.

In particular each of a set of smaller primes of positive reciprocal mass has $\gg p^{1+\theta}$ different larger prime neighbors **in its own introduction block**, already at one fixed cofactor. These give $\gg_\epsilon p^{1+\theta}$ different mixed supports per smaller prime, since $pqd\le k$ contains at most $1/\delta$ primes exceeding $k^\delta$. A uniform $p^{1+o(1)}$ support bound per digit per biconnected block in one witness for each full-period set therefore suffices for upper coefficient $1/2$ on this class. Even unbounded counts at small primes do not affect this last implication if the bound holds uniformly for all sufficiently large primes. The ordinary examples realize the leading coefficient in the class. The fixed [logarithmic order theorem](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/9411) has separate credit to dk8827, Star Fleet Math and Wouter van Doorn. Öztürk gives the unrestricted upper coefficient $3/2-\log 2$.

## Localizing the rows and their common cofactors

Use [component concentration](component-concentration.md) and its [row extraction](component-surplus.md). For some $\delta>0$ one net-positive component has $\gg\log k$ of reciprocal mass on integer rows $n\le k$ containing two distinct internal first-digit primes $>k^\delta$. Select just one such pair from each row, ordering it $p<q$, and write $n=pqd$. The pair has weight $w_pw_q$. For any fixed pair the sum of $1/d$ is at most $H_k$, by distinctness. All eligible vertices have total weight at most $M=2+\log(1/\delta)$ by Mertens' prime theorem. Write $b\log k$ for a lower bound on the selected row mass with $b>0$ fixed.

Root the block-cut tree of the component. Each digit is introduced in exactly one block. Each edge lies in a unique block, and all but at most one vertex of that block are introduced there. Discard pairs with an old endpoint in their edge block. Each new endpoint has at most one such old neighbor in its introduction block. Their total pair weight is at most $M k^{-\delta}$ and their row cost is at most $H_k M k^{-\delta}$. For each remaining pair both endpoints are introduced in its block. The sum, over blocks $J$, of the weights $m_J$ of eligible primes introduced there is at most $M$. The row mass in blocks with $m_J\le t$ is at most $H_k\sum m_J^2/2\le H_k tM/2$. Taking $t$ small leaves a positive multiple of $\log k$ on at most $M/t$ blocks. Keep the best one. Every selected internal support is a clique containing the selected pair's edge, hence belongs to that block, even if the integer modulus also tests earlier components.

The row mass of pairs with $p<q\le p^{1+s}$ is at most
$$
 H_k\sum_p w_p\sum_{p<q\le p^{1+s}}w_q
 \le H_k M\big(\log(1+s)+o(1)\big).
$$
The error is uniform for $p>k^\delta$ by Mertens' theorem. Choose a sufficiently small fixed $s>0$. Divide the interval $[\delta,1]$ of logarithmic exponents into fixed-length bins of width less than $s\delta/8$. Keep a pair of bins carrying a positive multiple of $\log k$ of the remaining mass. The gap between the bins is at least $3s\delta/4$ in exponent, so every cross pair satisfies the asserted power separation for some $\theta>0$. Remove $d<k^\beta$ at cost at most $M^2 H_{\lfloor k^\beta\rfloor}$. Choose $\beta>0$ small. A positive multiple of $\log k$ survives all these restrictions.

For these two bins and this block let $G_d$ have the selected pairs at cofactor $d$ as its edges. Then $\sum e(G_d)/d\gg\log k$ and $e(G_d)\le M^2$. Since $\sum_{k^\beta\le d\le k}1/d\le H_k$, the cofactors with $e(G_d)$ greater than some constant have total reciprocal weight $\gg\log k$.

For the simultaneous conclusion, draw $r$ cofactors independently with weights proportional to $1/d$ on all integers in the given range. For a given cross pair let $f$ be the probability its edge is present in one draw. The weighted sum of $f$ over the possible pairs is bounded below by a positive constant. Jensen's inequality for $f^r$, with total pair weight at most $M^2$, bounds the expected edge weight of the intersection below by a positive constant depending on $r$. The chance of any repeated draw is $O_r(k^{-\beta}/\log k)$, since the normalizing sum is asymptotic to $(1-\beta)\log k$. Boundedness of edge weight then gives a positive probability of distinct draws with intersection edge weight bounded below. Undo the normalization to obtain the stated tuple weight.

For growing $r$ the Jensen lower bound is at least $u v^r$ for some fixed $u>0$ and $0<v<1$, since the two bin weights are bounded and their product is bounded below by the original positive edge weight. Choose $0<z<\min(\beta/4,\delta/4,\delta\theta/4)$. With $r=\lfloor c_0'\log k\rfloor$ for $c_0'>0$ sufficiently small, the expected intersection weight is at least $2k^{-z}$. The collision loss, even multiplied by $M^2$, is $o(k^{-z})$. Distinct draws therefore give a common graph of weight at least $k^{-z}$. In the extraction below $D\gg k^{-z}$, $a\gg k^{-z}$ and $h\gg k^{-2z}$. Atoms are at most $k^{-\delta}$. Erasing at most $k^{(\delta-2z)/2}$ vertices costs $o(h)$ and leaves both sides nonempty and the graph connected. A smaller prime $p$ has at least $D p^{1+\theta}$ neighbors before deletion, which exceeds $p^{1+\theta/2}$ for large $k$ by the choice of $z$.

## Extracting a graph that survives deletions

Here is the finite weighted graph argument. It uses the minimal dense subgraph method familiar from Mader's connectivity theorem. The product edge weights are important. [Diestel, *Graph Theory*, Chapter 1](https://www.math.hkust.edu.hk/~mabfchen/Math4821B/Graph%20Theory%20by%20Diestel.pdf)

Suppose a simple graph has vertex weight at most $M$ in total and edge weight at least $g>0$. Set $D=g/(2M)$ and $a=D/8$. Select an inclusion-minimal induced subgraph of weight $W\ge2a$ satisfying $e>D(W-a)$. The full graph qualifies since $e\le W^2/2$ and $e\ge g$. No set with $2a\le W\le4a$ qualifies, since $W^2/2\le 2aW\le D(W-a)$. Removing any one vertex leaves weight at least $2a$: otherwise all edges meet the remaining set of weight less than $2a$ and $e<2aW<D(W-a)$. Minimality now shows every vertex has neighbor weight greater than $D$.

Consider a cut with smaller side of weight $x$. If $x<2a$, summing weighted degrees there and subtracting twice the internal edges gives crossing weight at least $(D-x)x$. Otherwise both sides meet the cutoff and minimality bounds their internal edge weights by $D(x-a)$ and $D(W-x-a)$. Subtract from $e$ to get crossing weight greater than $Da$. This proves expansion with constant $h=\min(D-2a,2Da/M)$. Both color classes have weight greater than $D$. After erasing a vertex set $Z$, for the smaller remaining side $A$ apply the old cut to $A$ versus the rest. At most $w(A)w(Z)$ crossing weight disappears. Each surviving vertex loses neighbor weight at most $w(Z)$. These bounds justify the asserted uniform erasures.

This argument supplies necessary structure under the hypothesis of a gain. The unresolved step is to exploit the many inescapable, fixed-cofactor graphs in a single rigid block to build a proper subcover, or to exhibit an irreducible family sustaining them. Weighted expansion and a common integer cofactor are compatible as arithmetic data alone.

[Exact weighted-graph and arithmetic checks](support-endpoint-check.py).
