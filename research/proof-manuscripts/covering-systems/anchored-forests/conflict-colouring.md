# A necessary obstruction on larger residual alphabets

Codex (OpenAI), 27 November 2026. Written deduction for future work.

Give each vertex of a loopless prime-coordinate multigraph $G$ exactly $p-d$ unary rows, where $p$ is its prime and $d\ge2$ is fixed across the component. Each edge carries one forbidden pair, including separate pairs on parallel edges. Suppose every assignment of all ordinary rows misses some tuple and one assignment misses exactly one tuple. Write $v=|V(G)|$, and let $\mu$ bound pair multiplicities. Let $\chi_{\rm sc}$ be the single-conflict chromatic number of Dvořák, Esperet, Kang and Ozeki. This is the least number of labels at each vertex for which every system of one local forbidden pair per edge has a surviving labeling.

There is a subgraph $H$ with
$$
 \chi_{\rm sc}(H)=\chi_{\rm sc}(G)=d,\qquad
 e(G)\ge (d-1)v+e(H).
$$
More precisely $G\setminus H$ contains $d-1$ distinct edges assigned to each vertex and no edge assigned to two vertices. For each connected component the assertion holds separately.

Indeed, the unary rows can retain any chosen $d$ labels, so $\chi_{\rm sc}(G)\le d$. In the unique-hole placement restrict to $d$ residual labels including that hole, and call its label zero everywhere. For each vertex and each of its $d-1$ nonzero labels, the tuple differing from zero there alone requires a row forbidding that nonzero label and zero at the other end. These edges are all distinct, since the all-zero tuple survives. Retain in $H$ only those edges whose forbidden pair has two nonzero labels in the chosen alphabet. The assignment on $H$ has no solution when all vertices use the $d-1$ nonzero labels: any solution would give another full tuple. Thus $\chi_{\rm sc}(H)>d-1$. Monotonicity gives the equalities.

Three quantitative consequences help distinguish small candidates.

* Density on the product grid gives $e(H)\ge(d-1)^2$. If $G$ is simple and $d\ge3$, choose a uniform pair of nonzero labels independently at each vertex. For every selection the restricted graph of active pairs is binary unsatisfiable. It has at least six edges by Karve–Hirani's forbidden-subdivision theorem (the smallest obstructions have six). Each edge is active with probability $4/(d-1)^2$. Hence $e(H)\ge 3(d-1)^2/2$.
* Theorem 4 of Dvořák et al. gives $d\le C(\mu e(H))^{1/4}\log(\mu e(H))$ when $e(H)\ge3$. In particular $\mu e(H)\gg d^4/(\log d)^4$ for growing $d$. A high-alphabet construction with few parallel rows needs that many *extra* pair rows after paying for every one-site change.
* Their Proposition 6 bounds the average degree of every subgraph of $G$ by $O(d^2\log(2d))$ since its single-conflict chromatic number is at most $d$. Combining the inequalities forces $|V(H)|\gg d^2/(\mu(\log d)^5)$ as $d$ grows. The bound on the genus in their Theorem 1 can likewise be applied to $H$.

These are consequences of published graph-colouring bounds and the one-hole condition. They are necessary conditions at fixed uniform residual alphabet, and leave arbitrary residual sizes and higher-arity rows open. A prospective construction must preserve the single-conflict chromatic number after assigning the $(d-1)v$ separate one-site exclusions. The exact binary case is [classified here](binary-graphs.md). [Dvořák–Esperet–Kang–Ozeki, Theorem 4 and Proposition 6](https://arxiv.org/pdf/1803.10962) · [Karve–Hirani](https://doi.org/10.1016/j.dam.2019.12.017)
