# Concentration of the actual reciprocal surplus

Codex (OpenAI), November 27, 2026. AI-authored supplement to the [component factorization and reciprocal theorem](component-surplus.md).

The component containing a large grid can itself be required to contribute a positive multiple of $\log k$ **after paying for all its own digit positions**. Thus a fixed leading gain cannot be assembled from arbitrarily many components that each contribute $o(\log k)$.

In any successful assignment of a full-period irreducible set, write
$$
 s_C=\sum_{r:C(r)=C}\frac1{n_r},\qquad
 \phi_C=\sum_{(p,j)\in C}\frac{H_{p-1}}{p^j}.
$$
For every $\epsilon>0$ there is $\nu>0$ such that if $S-\Phi(L)\ge\epsilon\log k$ and $k$ is sufficiently large, there is a component $C$ with
$$
                     s_C-\phi_C\ \ge\ \nu\log k.
$$
That particular component contains the common-cofactor grid and the subgraph of polynomial minimum degree in the main theorem, with constants depending only on $\epsilon$. In particular it contains polynomially many distinct moduli from the original cover. The component chosen can depend on the covering assignment.

**Proof.** The accounting through the section on where the surplus must be carried holds on every subcollection $\mathcal A$ of components, with the same error, measured using the original $k$. To see this directly, use global distinctness for the small smooth internal supports and sum the one-large-prime allowances only over first digits actually in $\mathcal A$. The discarded modulus and smooth-part errors were upper bounds for arbitrary subsets of the moduli. Thus, writing $\mathcal M$ for the retained rows with at least two internal primes $>k^\delta$,
$$
 \sum_{C\in\mathcal A}(s_C-\phi_C)
 \le e(\delta,k)\log k+
       \sum_{r\in\mathcal M,\ C(r)\in\mathcal A}1/n_r,
 \qquad \lim_{\delta\downarrow0}\limsup_{k\to\infty}e(\delta,k)=0.
$$
The estimate is uniform in the cover, assignment, and choice of $\mathcal A$.

Choose $\delta$ to make the error at most $(\epsilon/8)\log k$. Let $m_C$ be the reciprocal sum of all primes $p>k^\delta$ whose first digits belong to $C$, and put $M_0=1+\log(1/\delta)$. Then $\sum m_C\le M_0$ for large $k$. Every retained mixed row has two such primes in its own component. The reciprocal mass of all moduli containing a given pair $p,q$ is at most $H_k/(pq)$ by distinctness and the cutoff $n\le k$. Within $C$ its mixed mass is therefore at most $H_k m_C^2/2$.

Apply the uniform estimate to the union of components with $m_C\le t$. Their combined excess is at most $(\epsilon/8)\log k+(H_k/2)tM_0$. Choose $t>0$ sufficiently small in terms of $\epsilon,M_0$ to make this at most $(\epsilon/4)\log k$. As $\sum_C(s_C-\phi_C)=S-1/L-\Phi(L)$, the other components contribute at least $(\epsilon/2)\log k$ for large $k$. There are at most $M_0/t$ of them. At least one has the asserted positive excess with $\nu=\epsilon t/(2M_0)$. Since $s_C$ is bounded by the harmonic number at its row count, that count is at least $\exp(\nu\log k-1)$.

Finally reapply the uniform estimate to this single component, now choosing a new smaller threshold in terms of $\nu$. Its own retained mixed rows carry at least $(\nu/2)\log k$. All pair weighting, pruning, shared-cofactor extraction, and small erasure allowances from the main theorem now take place in this same component. The two thresholds need not coincide.

**Remaining issue.** This component is an indexed list of internal supports for which every reassignment leaves a hole and every deletion leaves at least two. Its actual integer moduli can include earlier digit conditions. Removing those conditions can identify moduli and change their reciprocal weights. Also, fixing small digits at the final hole can deactivate rows. Either operation needs a separate argument before it can be used to construct a standalone counterexample. A direct target is the mass that a single such list can retain with admissible distinct integer moduli.
