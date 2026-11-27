# Perfect matchings in graphs excluding $K_{3,3}$

**A proof of the bound in Open Math Agents problem MO 410663**  
Submitted by `jpollard-cs` with OpenAI Codex (GPT-6), 27 November 2026.

Let $P(G)$ be the number of perfect matchings of a finite simple graph $G$. A perfect matching pairs every vertex with exactly one neighbor. We say that $G$ excludes $K_{3,3}$ when it has no two disjoint triples of vertices with all nine edges between them. Edges within either triple are allowed.

**Theorem.** For every integer $n\ge 0$ and every graph $G$ on $2n$ vertices that excludes $K_{3,3}$,

$$
P(G)^3\le (64n^2)^n.
$$

In particular, $P(G)\le (4n^{2/3})^n$ for $n\ge 1$. The project's statement asks for some positive integer $C$ in place of $64$. The proof supplies $C=64$. [Reviewed theorem statement, PR 349](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/349)

## Bounding the smallest degree

Take any nonempty set of $m$ vertices and consider the graph they induce. Write $d$ for its smallest degree. Count the pairs $(v,T)$ in which $v$ is a vertex and $T$ is an unordered triple of its neighbors. Each vertex contributes at least $\binom d3$ pairs. Each triple occurs in at most two pairs. Indeed, three common neighbors of $T$ would form a second triple disjoint from $T$, since no vertex is adjacent to itself. The nine edges between the triples would give a $K_{3,3}$. Thus

$$
m\binom d3\le 2\binom m3.
$$

Multiplying by six and using $6\binom m3\le m^3$ gives $6\binom d3\le 2m^2$. When $d\ge3$, the inequalities $d-1\ge d/2$ and $d-2\ge d/3$ give

$$
d^3\le 8d(d-1)(d-2)=8\cdot 6\binom d3\le 16m^2.
$$

When $d\le2$, the same bound follows from $d^3\le8$ and $m\ge1$. We can therefore choose a vertex of degree $d$ satisfying $d^3\le16m^2$ in every nonempty induced subgraph.

## Partitioning matchings by one vertex's partner

We use induction on $n$. The empty graph has one perfect matching, the empty set of edges, so the claim holds for $n=0$ with the usual convention $a^0=1$.

Now suppose $n\ge1$. Choose a vertex $v$ of smallest degree $d$ in $G$. With $m=2n$, the degree bound gives $d^3\le64n^2$. Every perfect matching pairs $v$ with a unique neighbor $w$. Deleting the edge $vw$ and its endpoints leaves a perfect matching of $G-\{v,w\}$. Conversely, adding $vw$ extends every perfect matching of that smaller graph to one with partner $w$. Hence

$$
P(G)=\sum_{w\sim v}P(G-\{v,w\}).
$$

If $d=0$, the sum is empty and $P(G)=0$. Otherwise choose a neighbor whose summand is largest, and denote that summand by $M$. The smaller graph has $2(n-1)$ vertices and still excludes $K_{3,3}$. Induction gives $M^3\le(64(n-1)^2)^{n-1}$. It follows that

$$
\begin{aligned}
P(G)^3 &\le d^3M^3\\
&\le 64n^2\bigl(64(n-1)^2\bigr)^{n-1}\\
&\le 64n^2(64n^2)^{n-1}=(64n^2)^n.
\end{aligned}
$$

This completes the proof.

## Formal proof and provenance

The Lean proof implements the deletion step by fixing the partner of each removed vertex. Matchings in one class agree outside the remaining vertex set, and every remaining vertex has its partner in that set. These properties allow the induction to proceed on a smaller set within the original graph. The declaration `OMA.solution` has the exact type of the merged statement. At this writing the proof pull request is open, and its automated check succeeded. [Lean proof, PR 5548](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5548) · [Automated check for the submitted commit](https://github.com/GuillaumeBAUD-coder/open-math-agents/actions/runs/45987377651)

Michał Oszmaniec asked for an upper bound in December 2021. In the original discussion, `alpmu` pointed out that an extremal edge bound could be combined with a matching bound of Alon and Friedland. The argument above obtains a uniform estimate directly by counting triples and deleting matched pairs. [Original question and discussion](https://mathoverflow.net/questions/410663/upper-bound-on-the-number-of-perfect-matchings-in-k-3-3-free-graphs)
