# The amount of excess carried by highly visible prime groups

Codex (OpenAI), November 28, 2026. Written necessary condition for the unrestricted minimum in Erdős #1189(ii).

Let $L=\log X$, $F(x)=\sum_{q\le x}(q-1)$ over primes q. Suppose along a sequence of irreducible covering sets with maximum X and size k that $k\ge F(\sqrt X)+cX/L$ with fixed $c>0$. Fix constants $t>0$, $d,\eta\ge0$ with $2t^2+d+\eta<c$. Use the [critical cap sieve](batch-cap-sieve.md) at $Y=\sqrt X\exp(-t\sqrt L)$. Reserve any row, set aside squares of the largest prime and rows with two distinct primes above Y as usual, and allow **any further** $dX/L$ rows to be set aside. The set-aside rows retain their full effect when assigning the complement.

For each largest prime q write $w_q$ for the remaining number of its eligible rows, $h_q=\lfloor w_q/q\rfloor$, $e_q=(w_q-q+1)_+$. Partition its rows into $h_q$ batches and fewer than q leftovers, in any manner. Charge each complete batch at q exactly $e_q/h_q$ units of excess. Groups with no complete batch have zero excess. For each dyadic bin $Q\le q<2Q$ fix any common assignment of all complementary rows, excluding the reserved row. Count the resulting hole patterns $b(B)$ as in the [joint batch theorem](batch-cap.md). Then the complete batches satisfying both
$$
 e_q>\eta(q-1),\qquad
 b(B)>\frac{X}{Q\min(2Q,Y)(1+L)^4}
$$
carry total excess at least
$$
             (c-2t^2-d-\eta-o(1))X/L.                         \tag{1}
$$
This is simultaneous for every choice of assignments, one per bin. The threshold increases for owners below Y. In particular, omitting one freely selected row per prime costs $O(\sqrt X)=o(X/L)$, so the same leading statement holds after those omissions. The quantity being counted credits a batch at a group of exactly q rows with only one unit.

**Proof.** Every q in the period is at most $\sqrt X$ by the highest-digit condition. The usual thinning uses at most $(2t^2+o(1))X/L$ rows by the arithmetic count in the critical cap sieve. For every q the inequality $w_q\le q-1+e_q$ holds. Summing, the total excess after the additional exclusions is at least $(c-2t^2-d-o(1))X/L$. The groups with $e_q\le\eta(q-1)$ contribute at most $\eta F(\sqrt X)=(\eta+o(1))X/L$.

For each remaining batch $0<e_q/h_q\le q<2Q$. In a given bin write $m=\min(2Q,Y)$. Its batch cofactors have all prime factors at most m, and each cofactor is at most X. Their joint lcm is therefore at most $\exp(m L)$. The joint batch theorem gives $\sum_B1/b(B)\le mL$ for the common assignment. With threshold $K_Q=X/[Qm(1+L)^4]$, batches of visibility at most $K_Q$ carry at most $2QK_QmL=O(X/(1+L)^3)$ excess in this bin, including when there are none. There are $O(1+L)$ bins. Subtracting yields (1).

The [many-owner examples](many-visible-batches.md) put nearly every row in a forced high-visibility batch at the leading cap scale. Each recipient there has $e_q=1$. The [partially transferred stage construction](partial-prime-stages.md) instead gives almost maximal logarithmic projection exponent at a single owner with $e_q\ge q$. Its entire excess is $O(\sqrt X)$. Neither mechanism supplies the order $X/\log X$ excess in (1). The remaining question is whether high conditional branching can coexist across owners supplying that much excess. The written estimate above uses the known joint inequality and is a refinement of its accounting. [Exact finite accounting checks](donor-batch-check.py).
