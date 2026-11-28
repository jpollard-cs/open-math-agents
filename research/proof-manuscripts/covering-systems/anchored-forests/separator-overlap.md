# Exact minimum intersection on a two-digit separator

Codex (OpenAI). Written proof and Lean verification accompanying the [separator gluing criterion](two-digit-separator.md).

Take any two sets of feasible cells in a $2\times q$ grid and fix the relative orientation of the two rows. For the first set let $a_0,a_1,a_2,a_3$ count empty columns, top-only columns, bottom-only columns and full columns. Define $b_i$ for the second set. Put
$$
 u=(a_1+a_3)+(b_1+b_3)-q,\qquad
 v=(a_2+a_3)+(b_2+b_3)-q.
$$
**Over all column bijections, the exact minimum number of common cells is**
$$
                \boxed{\max\{\max(u,0)+\max(v,0),\ a_3-b_0,\ b_3-a_0\}.}
$$
If the relative row orientation is free, take the lesser of this expression and the one with $b_1,b_2$ interchanged. This applies at every $q$, including profiles with repeated and empty columns. In a branch computation it counts joint feasible **boundary** cells. If each feasible cell has a unique private continuation in both branches, it counts full solutions as well. Use the [marked test](two-digit-separator.md) in the general unique-continuation case.

For example, on $2\times5$, let the first feasible set be one entire row and the second consist of two entire columns. Exactly two cells survive every independent relabeling, although the total sizes alone permit disjoint sets on ten abstract points. The formula measures the effect of the two separate digit permutations.

**Proof by transport on a square.** Represent the column masks as the four corners of $\{0,1\}^2$. Replace each right mask by its bitwise complement. For paired masks $a,b$ the elementary identity
$$
      2|a\cap b|=|a|-|\bar b|+\operatorname{dist}_1(a,\bar b)
$$
reduces the minimum to a transportation problem with Hamming distance on the four-cycle. The constant summed over the columns is $u+v$.

For completeness, given equal integer supplies and demands on a cycle, the minimum transportation distance is the minimum total absolute value of an integral edge flow with the specified net supplies. Any pairing gives such a flow along shortest paths. Conversely split a flow into unit paths from excess to deficit, canceling cycles, to obtain a pairing of no greater cost, and pair common masses at each vertex for zero cost. In a fixed cyclic orientation the flows on the four edges have the form $t+s_i$, where the four $s_i$ come from cumulative net supplies. A median of the integers $-s_i$ minimizes the total absolute value. Give the two largest resulting edge flows sign $+1$ and the other two sign $-1$, choosing signs at ties to get two of each. This signs each nonzero flow correctly. The signs sum to zero and therefore are gradients of a vertex potential, up to the convention for cyclic orientation. Discrete summation by parts shows its pairing with net supplies attains the optimal cost. Conversely any such potential gives a lower bound on cost by the triangle inequality.

Up to addition of a constant, the six potentials given by two positive and two negative cyclic gradients are $\pm x\pm y$ and $\pm(x\mathbin{\mathrm{xor}} y)$. Their maximum against net supply is
$$
  \max\big\{|u|+|v|,\ |(a_1+a_2)-(b_1+b_2)|\big\}.
$$
The parity coordinate is invariant under complementing both bits. Add $u+v$, divide by two, and use $\sum a_i=\sum b_i=q$ to get the displayed answer. This use of circular transportation is classical. [Rabin, Delon and Gousseau, *Transportation distances on the circle*](https://perso.telecom-paristech.fr/gousseau/matching.pdf)

**Independent formal proof.** [MinimumOverlap.lean](MinimumOverlap.lean) constructs a pairing directly by induction on the unrestricted number of columns. For a proposed integer budget $n$, its five linear inequalities say $a_3-b_0,b_3-a_0,u,v,u+v\le n$. With nonnegativity of $n$ these are exactly the boxed formula. After choosing any first left column, at least one of the four right types is available whose removal preserves the five inequalities with its intersection cost deducted. Lean checks these finite linear implications for all multiplicities by Presburger arithmetic, constructs the pairing recursively and proves necessity for every pairing. Thus the formal proof uses neither continuous transport duality nor a cycle-flow assumption. The separate [BinarySeparator.lean](BinarySeparator.lean) constructs the disjoint transportation table and verifies the horizontal split and $q-1$ capacity arithmetic from the branch obstruction.

Both sources use the Lean 4.33.1 standard library. Run with the toolchain bin directory on PATH:
    
    export LEAN_PATH=.
    lean -o BinarySeparator.olean BinarySeparator.lean
    lean -o MinimumOverlap.olean MinimumOverlap.lean
    leanchecker BinarySeparator
    leanchecker MinimumOverlap
    python separator-overlap-check.py

[Independent enumeration](separator-overlap-check.py) minimizes over actual column permutations and compares all histogram pairs through $q=5$ with the displayed expression. The general integer covering-set applications and the asymptotic bounds are written research. The local theorem does not impose the required profile shapes on every covering set.
