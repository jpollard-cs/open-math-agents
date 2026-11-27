# Counting perfect matchings in graphs without $K_{3,3}$

*Jordan Pollard, with OpenAI Codex (GPT-6), November 27, 2026*

A perfect matching pairs every vertex of a graph with one of its neighbors. Write $P(G)$ for the number of ways to do this. Suppose $G$ has $2n$ vertices and contains no copy of $K_{3,3}$. This means that no two disjoint triples have all nine edges between them. Edges within each triple are allowed. The checked theorem gives

$$
P(G)^3 \le (64n^2)^n .
$$

For $n\ge1$ this reads $P(G)\le (4n^{2/3})^n$. The factor $4$ comes from the explicit witness $64$ in the proof. The project statement asks for the existence of a constant. [Formal statement](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/df2ae918f9c0cf4366fca812a462382fcc83de1f/statements/mo-410663.lean#L20-L22), [MatchingCount.uniform_upper](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/c7f8ce950580ef6dd80e9924ebbf6749ddfdcc2d/proofs/mo-410663.lean#L179-L193)

## Find a vertex with few possible partners

Take any nonempty set of $m$ vertices and let $d$ be the smallest degree inside it. Count the pairs consisting of a vertex and three of its neighbors inside the set. Each vertex contributes at least $\binom d3$ pairs. Each triple occurs at most twice. A third common neighbor would give a copy of $K_{3,3}$, since none of the common neighbors can belong to the triple in a loopless graph. [MatchingCount.contains_of_triples](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/c7f8ce950580ef6dd80e9924ebbf6749ddfdcc2d/proofs/mo-410663.lean#L17-L41)

Thus $m\binom d3\le 2\binom m3$, so $6\binom d3\le 2m^2$. For $d\ge3$, the inequalities $d-1\ge d/2$ and $d-2\ge d/3$ give $d^3\le 8d(d-1)(d-2)\le 16m^2$. The same conclusion holds when $d\le2$, since $m\ge1$. For $n\ge1$, taking $m=2n$ gives a vertex with $d$ possible partners and $d^3\le64n^2$. [MatchingCount.small_degree](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/c7f8ce950580ef6dd80e9924ebbf6749ddfdcc2d/proofs/mo-410663.lean#L46-L90)

## Fix a partner and repeat

Choose such a vertex $v$. If it has no neighbor there are no perfect matchings. Otherwise divide all perfect matchings into classes according to the partner of $v$. If the largest class has size $M$, then $P(G)\le dM$. In that class, both $v$ and its partner are fixed. The same argument applies to the remaining $2(n-1)$ vertices. At zero remaining vertices a class has at most one matching, because every vertex's partner is fixed. [MatchingCount.mate_ext](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/c7f8ce950580ef6dd80e9924ebbf6749ddfdcc2d/proofs/mo-410663.lean#L92-L113), [MatchingCount.family_bound](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/c7f8ce950580ef6dd80e9924ebbf6749ddfdcc2d/proofs/mo-410663.lean#L115-L177)

Induction now gives $M^3\le (64(n-1)^2)^{n-1}$. Multiplying by $d^3\le64n^2$ proves the claimed inequality. Lean carries out the induction inside the original graph. The family of matchings agrees on every partner outside the remaining vertex set, and every partner of a remaining vertex is still inside that set. Fixing a pair preserves both properties. [Induction step](https://github.com/GuillaumeBAUD-coder/open-math-agents/blob/c7f8ce950580ef6dd80e9924ebbf6749ddfdcc2d/proofs/mo-410663.lean#L134-L177)

## Prior work and formalization

Michał Oszmaniec asked the question on MathOverflow in 2021. In that discussion, alpmu identified an existing route combining an extremal edge bound with the perfect-matching inequality of Noga Alon and Shmuel Friedland. Oszmaniec confirmed that it gave the bound he needed. Left to Solve classifies the result as known. The contribution here is a Lean formalization by direct counting and induction. The project credits Jordan Pollard (@jpollard-cs), using OpenAI Codex (GPT-6), for the statement and proof. Codex drafted this explanation. [Original discussion](https://mathoverflow.net/questions/410663), [Alon and Friedland](https://arxiv.org/abs/0803.2578), [Project review](https://lefttosolve.com/p/mo-410663), [Accepted proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5548)
