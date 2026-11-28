# The optimal ellipsoid and variance tradeoff on the EHPS block

OpenAI Codex, prepared for Jordan Pollard, 27 November 2026  
AI-generated research manuscript for public review.

Let $T_\epsilon$ be the two-dimensional torus block in Definition 4.1 of Elsholtz, Hunter, Proske and Sauermann (EHPS). Fix a positive definite quadratic form $Q$ on $\mathbb R^2$, with the same symbol for its matrix. A real measurable potential $H$ is admissible if, for all $x,y,z\in T_\epsilon$ with $x+z\equiv2y\pmod 1$,
$$
 H(x)+H(z)-2H(y)\ge Q(x-z).
$$
Differences use the representatives in $[0,1)^2$. Let $\sigma(H)$ denote standard deviation under uniform measure on $T_\epsilon$. We consider potentials with finite second moment. All implied constants below are positive and absolute.

**Theorem.** As $\epsilon\downarrow0$,
$$
 \sup_{Q,H}\frac{\sqrt{\det Q}}{\sigma(H)}\asymp\epsilon.
$$
For the Euclidean form, every such $H$ has mean absolute deviation from any constant at least a constant times $\epsilon^{-2}$. This variation already occurs on a fixed rectangle strictly inside one component, independent of $\epsilon$. The EHPS potential attains the order $\epsilon^{-2}$.

We also bound the actual measure of every single slice at the ellipsoid volume budget. It applies to arbitrary measurable potentials, rotated ellipsoids and products whose blocks have different parameters. The extremal order of $r_3(N)$ remains open.

## 1. Two representatives with the same potential

Use $s=a+b$ and a parameter $t$. On the high band $7/6+\epsilon\le s\le17/12$ write
$$
 X_s(t)=(t+1/2,s-t-1/2),\qquad Z_s(t)=(t,s-t).
$$
We use $X$ in EHPS region $T_2$ and $Z$ in $T_3$. When both are present, their potentials agree. Indeed, their difference is $(1/2,-1/2)$, so each serves as a modular midpoint for two copies of the other. Both inequalities have right side zero. Denote $H(X_s(t))$ by $F(s,t)$. On the interior of the convex polygon $T_2$, the function $F$ is convex. Ordinary midpoint triples give midpoint convexity. Local integrability bounds $F$ above on compact subsets by averaging the midpoint inequality over a small ball. Dyadic interpolation then gives ordinary convexity: to obtain continuity at a point, take successively doubled displacements inside a neighborhood of bounded upper values in the dyadic midpoint inequality. This bounds upward increments by a constant times the length of the displacement. Applying the midpoint inequality at opposite displacements gives the lower bound.

Set $I=[19/16,6/5]$, take $0<e=\epsilon\le1/1000$, and define
$$
 L_s=s-1+e,\quad W_s=L_s+1/4,\quad U_s=3/2+2e-s,
 \quad T=1/2-e,\quad h=5e/2.
$$
For $s\in I$, all four upper-sheet points $X_s(L_s),X_s(W_s),X_s(U_s),X_s(T)$ and the three lower-sheet points with parameters $W_s,U_s,T$ belong to the block. To see this, the upper sheet at these coordinates requires $s-1<t<1/2$. The lower sheet additionally requires $t+s\ge3/2+e$. These inequalities follow from $W_s\ge7/16$, $U_s+s=3/2+2e$, and $T\ge 499/1000$, together with $L_s>s-1$. In particular $L_s<U_s<W_s<T$.

Put $P(s)=F(s,T)$ and $k=Q(1,-1)/8$. The ordinary midpoint of $X_s(W_s)$ and $Z_s(W_s)$ is $X_s(L_s)$. Equality of their endpoint potentials gives
$$
 F(s,W_s)\ge F(s,L_s)+k .
$$
Convexity along $t$ now gives $P(s)\ge F(s,W_s)$ and $P(s)\ge F(s,U_s)$. In particular $F(s,L_s)\le P(s)-k$.

Whenever $s-h,s+h\in I$, the ordinary midpoint of $X_{s-h}(L_{s-h})$ and $Z_{s+h}(U_{s+h})$ is $Z_s(T)$. The first coordinate is $1/2+3e/2-h=T$, and the coordinate sum is $s$. Dropping the nonnegative right side of its midpoint inequality gives
$$
 2P(s)\le F(s-h,L_{s-h})+F(s+h,U_{s+h}).
$$
Combining the two relations yields the uniform second difference
$$
 P(s-h)+P(s+h)-2P(s)\ge k. \tag{1}
$$

## 2. The variation reaches the interior

Let $K=I\times[29/100,46/100]$ in $(s,t)$ coordinates. Both $(s,W_s)$ and $(s,U_s)$ are in $K$. For $s$ at distance at least $h$ from the ends of $I$, the preceding inequalities show
$$
 \inf_K F\le P(s)\le \sup_K F.
$$
For the lower estimate use $F(s,W_s)\le P(s)$. For the upper estimate replace $F(s-h,L_{s-h})$ by $F(s-h,W_{s-h})-k$ in the last midpoint inequality.

For sufficiently small $e$, there are $2m+1$ consecutive points spaced $h$ apart in the interval obtained by trimming $h$ at both ends of $I$, where $m\gg 1/e$. Multiply (1) at the interior indices $j$ by $\min(j,2m-j)$ and sum. All coefficients cancel except $1,-2,1$ at indices $0,m,2m$, and the weights sum to $m^2$. Thus
$$
 \sup_K F-\inf_K F\ge m^2 k/2\gg e^{-2}Q(1,-1).
$$
The same oscillation also bounds an integral from below. Let $D=(1.18,1.21)\times(0.28,0.47)$, which lies strictly inside the upper sheet for every $e$ under discussion. Fix $\rho>0$ with $K+B(0,2\rho)\subset D$. For any constant $c$, midpoint convexity gives
$$
 |F(p)-c|\ll_\rho\int_D |F-c|\quad(p\in K).
$$
For the upper bound, average $2F(p)\le F(p+v)+F(p-v)$ over $|v|<\rho$. For the lower bound average $F(p)\ge2F(p+v)-F(p+2v)$ over the same ball. The coordinate map from $D$ to the upper sheet has absolute Jacobian one. We obtain
$$
 \int_D|F-c|\gg e^{-2}Q(1,-1). \tag{2}
$$
This step prevents large potential values confined to a very narrow boundary strip from accounting for (1).

There is also a bound proportional to $\lambda_{\max}(Q)$. Inside the physical image of the interior of $K$, place an ordinary midpoint triple with fixed sufficiently small endpoint distance in a unit eigenvector direction for this eigenvalue. Its midpoint inequality gives $\operatorname{osc}_K F\gg\lambda_{\max}(Q)$. The same integral estimate applies.

Write $\alpha$ and $\gamma$ for the diagonal entries of $Q$ in the orthonormal directions $(1,-1)/\sqrt2$ and $(1,1)/\sqrt2$, respectively. Taking $c$ equal to the uniform mean and using Cauchy–Schwarz shows
$$
 \sigma(H)\gg \max\{e^{-2}\alpha,\gamma\}
    \ge e^{-1}\sqrt{\alpha\gamma}\ge e^{-1}\sqrt{\det Q},
$$
with the implied constant on the first inequality carried throughout. Conversely the EHPS potential $f$ plus $2e^{-2}s^2$ is admissible for $Q(u)=|u|^2+e^{-2}(u_1+u_2)^2$. EHPS Proposition 2.2 and Lemma 4.4 give this by the ordinary quadratic midpoint identity and $0\le s(y)\le(s(x)+s(z))/2$. Its standard deviation is at most $108e^{-2}$, while $\sqrt{\det Q}=\sqrt{1+2e^{-2}}$. This proves the theorem.

## 3. Optimizing products of different blocks

Let $d=2m$, use independent blocks with parameters $e_i\in(0,1)$, forms $Q_i$ and potentials $H_i$, and put $A=7/24$. Write $a_i=|T_{e_i}|$, $b_i=\sqrt{\det Q_i}$, and $\sigma_i=\sigma(H_i)$. For a product slice of width $\Delta$, the endpoint difference is in $\sum_i Q_i(u_i)\le 2\Delta$. Its volume is $(2\pi\Delta)^m/(m!\prod b_i)$. The union bound for a random torus line of length $N$ therefore allows width a constant times $m(\prod b_i)^{1/m}N^{-1/m}$. The variance of the sum of the potentials is $\sum\sigma_i^2$. Concentrating by Chebyshev and partitioning the central interval gives the following expression, up to constant factors, for the size certified by this calculation:
$$
 N\prod a_i\ \min\!\left\{1,\frac{m(\prod b_i)^{1/m}N^{-1/m}}{(\sum\sigma_i^2)^{1/2}}\right\}.
$$
The estimate $b_i/\sigma_i\ll e_i$ extends to $e_i$ bounded away from zero because the parameter-independent open region $T_1$ contains a disk. An ordinary midpoint triple in its interior and the integrated midpoint bounds used in section 2 give $\sigma_i\gg\lambda_{\max}(Q_i)$ there.

For small $e$, $|T_e|\le A-e/12$. Indeed the strip $3/4\le a\le5/6$, $7/6<a+b<7/6+e$ lies in the limiting upper sheet and is removed. The zero-margin area is $A$ by EHPS Definition 4.1 and its area computation. Monotonicity therefore gives $a_i\le A\exp(-c e_i)$ on the full parameter interval for an absolute $c>0$. AM–GM bounds the root-sum-square below by $\sqrt m(\prod\sigma_i)^{1/m}$ and bounds the geometric mean of the $e_i$ by their arithmetic mean. Writing $u=\sum e_i$ gives the upper estimate on the displayed expression
$$
 \ll N A^m m^{-1/2}N^{-1/m}\,u e^{-cu}
 \ll N A^m m^{-1/2}N^{-1/m}.
$$
Identical blocks with margin $A/(2m)$ and the sum-direction ellipsoid attain this order, as shown in the companion paper. This proves sharpness of the polynomial factor within the variance and Euclidean volume calculation. The next section treats the actual level-set probabilities.

## 4. An upper bound for the mass of an actual slice

The same order is sharp even if the most populated interval of values of the product potential is selected by exact measurement. Suppose that the width $\Delta$ obeys the ellipsoid volume budget $N\operatorname{vol}(E)\le 1$ from section 3. For every interval $J$ of width $\Delta$ we claim that
$$
 N\left|\left\{(x_i)\in\prod T_{e_i}:\ \sum_i H_i(x_i)\in J\right\}\right|
 \ll N A^m m^{-1/2}N^{-1/m}. \tag{3}
$$
The companion construction attains this order. This is an upper bound for a single product-potential slice under the stated volume budget.

**A bounded density for each block.** Write $b=\sqrt{\det Q}$. On each of the three convex component polygons, transform the coordinates by $Q^{1/2}$. In the transformed coordinates $w$, the function $H-2|w|^2$ is convex by the midpoint inequality. Extend it by lower semicontinuous closure on the closed polygon, then add back $2|w|^2$. This leaves interior values unchanged. An affine support at an interior point supplies a finite lower bound, and compactness gives a minimizer $w_0$. Along a ray from $w_0$, write $H(r)=H(w_0+r\theta)$. The function $H(r)-2r^2$ is convex and has nonnegative right derivative at zero since $H(0)$ is minimal. It is therefore nondecreasing. Thus an interval of width $\delta$ captures at most $\delta/4$ in radial area $r\,dr$ on this ray. Integration over angles gives area at most $\pi\delta/2$ on one transformed polygon. The three components, the Jacobian $b$ and $|T_e|\ge 7/36$ give a density bound $C/b$ for the law of $H$ under uniform sampling.

**A component with a smaller density.** By section 2, the oscillation on $K$ is at least $c b/e$ for small $e$. Select $p,q\in K$ with $F(q)-F(p)\ge c' b/e$. A supporting affine function for $F$ at $q$ gives a half-disk of fixed radius in $D$ where $F\ge F(q)$. Its mass under uniform sampling from $T_e$ is bounded below by an absolute constant. Along a ray from $p$ the one-variable convex function increases with slope at least $c''b/e$ wherever its value reaches $F(q)$, by the secant slope from $p$ and the bounded diameter of $D$. Hence an interval of width $\delta$ captures at most $C\delta e/b$ area in that half-disk by polar integration. Restricting to the half-disk and, if necessary, taking a constant fraction of its measure produces a mixture component of some fixed probability $p_0>0$ with normalized density at most $Ce/b$. The normalized residual density is at most $C/b$ by the preceding paragraph, choosing $p_0\le1/2$. For $e$ bounded away from zero the first density bound suffices for either component of a mixture of two copies of the full law.

**Sums of different blocks.** We use the one-dimensional bounded-density projection theorem of Rudelson and Vershynin. In the form needed here, if independent variables have densities bounded by $C/v_i$ with $v_i>0$, their sum has density at most $C'/(\sum v_i^2)^{1/2}$. This follows by scaling the variables by $1/v_i$ and normalizing the vector of coefficients to unit length.

Set $u_i=\max(e_i,1/m)$, $r_i=b_i/u_i$. Choose the mixture labels independently with success probability $p_0$. A successful component has density at most $C/r_i$ and any remaining component has density at most $Cm/r_i$. Let $V_i$ be $1$ on success and $1/m^2$ otherwise. Conditional on the labels, the density of the sum is bounded by $C(\sum r_i^2 V_i)^{-1/2}$.

For clarity, the bound remains uniform even for very unequal $r_i$. Put $\phi(t)=\mathbb E e^{-tV_1}$. Using the integral for $x^{-1/2}$ and applying Hölder with $m$ equal exponents against $t^{-1/2}dt$ gives
$$
 \mathbb E\left(\sum r_i^2V_i\right)^{-1/2}
 \le (\prod r_i)^{-1/m}\,\mathbb E\left(\sum V_i\right)^{-1/2}.
$$
Indeed, the product integrand is $\prod_i\phi(t r_i^2)$, and the change of variable in the $i$th Hölder integral gives the factor $1/r_i$. With probability at least $1-e^{-c m}$ at least $p_0m/2$ labels succeed, by the binomial tail bound. On the complementary event $\sum V_i\ge 1/m$. Consequently the final expectation is $O(m^{-1/2})$, including small $m$ by adjusting the constant.

The probability is at most $C\Delta/(\sqrt m(\prod r_i)^{1/m})$. The budget gives $\Delta\le C m(\prod b_i)^{1/m} N^{-1/m}$. Multiplying by the product area and using $(\prod u_i)^{1/m}\le (1+\sum e_i)/m$ now proves (3), since $(1+\sum e_i)\exp(-c\sum e_i)$ is bounded. This result concerns the measure of the slice. An exceptional line or translate can in principle meet a set in more than its Haar average, and other avoidance arguments can use a different width budget.

## Verification and sources

The accompanying Python script builds exact nonnegative rational combinations of midpoint inequalities on finite grids. It represents every interpolation inequality by its positive combination of consecutive ordinary midpoint triples, uses equal-endpoint triples for both sheet identifications, and checks the final three nonzero coefficients. The analytic statements have written proofs. External review and priority remain open.

1. C. Elsholtz, Z. Hunter, L. Proske and L. Sauermann, *Improving Behrend's construction*, Definition 4.1, Proposition 2.2 and Lemma 4.4. [arXiv:2406.12290](https://arxiv.org/abs/2406.12290).
2. OpenAI Codex, *A logarithmic refinement for integer sets avoiding three-term progressions*, companion manuscript and checks. [Public review](https://github.com/jpollard-cs/open-math-agents/tree/d8ca3c980ef0f8f205b61acc1315507ba65e19a4/research/proof-manuscripts/erdos142-ellipsoid).

3. M. Rudelson and R. Vershynin, *Small ball probabilities for linear images of high-dimensional distributions*, Theorem 1.2. [Author-hosted paper](https://public.websites.umich.edu/rudelson/papers/rv-smallball.pdf).
