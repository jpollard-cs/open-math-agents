# Testing the leading coefficient on finite period surpluses

Codex (OpenAI). Written corollary of the [linear-size transfer](linear-full-period.md) for Erdős #1189.

The transfer makes it sufficient for a proposed counterexample to gain a positive multiple of $\log k$ **over the ideal mass of its own period**, even if that period is inefficient for its size. More precisely put
$$
  G(k)=\max_{|D|=k}\left(S(D)-\Phi(\operatorname{lcm}D)\right)
$$
over irreducible covers, with the notation of the [main note](linear-full-period.md). Write $G_*(k)$ for the same maximum with the period required to be a member of $D$. For each operator $\mathcal L\in\{\liminf,\limsup\}$,
$$
 \mathcal L\,\frac{R(k)}{\log k}
 =\mathcal L\,\frac{R_*(k)}{\log k}
 =\frac12+\mathcal L\,\frac{G(k)}{\log k}
 =\frac12+\mathcal L\,\frac{G_*(k)}{\log k}.
$$
In particular a slowly divergent additive surplus does not by itself settle the coefficient. The necessary and sufficient test for upper coefficient $1/2$ is the uniform upper bound $S(D)-\Phi(\operatorname{lcm} D)\le o(\log |D|)$ over full-period sets. A family with surplus at least $\eta\log |D|$ for fixed $\eta>0$ gives an unrestricted upper limiting coefficient at least $1/2+\eta$.

**Proof.** The uniform period knapsack estimate gives $\Phi(\operatorname{lcm} D)\le R_0(k)+o(1)$, hence $G(k)\ge R(k)-R_0(k)-o(1)$ and likewise with stars. In the other direction choose an input attaining $G(k)$ in the proof of the linear-size transfer. Its full-period output before padding has ordinary mass minus ideal mass at least $G(k)-1$ by the exact binary accounting. The missing-position construction proves, for $u=K-3k-1\to\infty$,
$$
                           R_*(K)\ge G(k)-1+R_0(u)-o(1).
$$
Thus an input with positive normalized surplus need not have its own reciprocal sum above $R_0(k)$. When extracting the upper limit take $K=6k+2$. For the lower limit use every $K$ and $k=\lfloor(K-2)/6\rfloor$. Then $\log k\sim\log u\sim\log K$ and $R_0(u)/\log u\to1/2$. Since $S(D)\le H_{k+1}$ and $\Phi\le R_0(k)+o(1)$ all normalized quantities are bounded. These comparisons and $G_*\le G$, $R_*\le R$ prove the four equalities. The zero-defect family gives unrestricted lower coefficient at least $1/2$.

The actual supremum of these normalized surpluses at large size remains undetermined. The earlier [additive variational formula](unrestricted-transfer.md) concerns an unnormalized supremum and does not control its rate of growth.
