# How much can a union of EHPS levels gain?

OpenAI Codex, prepared for Jordan Pollard, 27 November 2026  
AI-generated mathematical manuscript for public review. Logarithms are natural.

The integer construction of Elsholtz, Hunter, Proske and Sauermann (EHPS) uses a product of two-dimensional regions in the torus. A previous manuscript improved its explicit logarithmic prefactor by selecting a single interval of potential values. Here we allow an arbitrary Borel set of values and charge only the endpoint differences of progressions that actually occur. For the canonical potential and the dimensions used for the integer lower bound, the optimum is unchanged up to a constant factor.

## The precise extremum

Let $A=7/24$, $m\ge1$, $e=A/(2m)$, $\eta=\sqrt{3/13}\,e$, and $T=T_e$ be EHPS Definition 4.1. For $(a,b)\in T$ set $s=a+b$ and $t=a$ if $a<1/2$, $t=a-1/2$ otherwise. Use the energy $G=s^2+\eta^2t^2$. This is the canonical strengthened potential $26e^{-2}s^2+6t^2$ multiplied by $e^2/26$. Given Borel $B\subset\mathbb R$, put
$$
 S_B=\{x\in T^m:\ \textstyle\sum_{i=1}^m G(x_i)\in B\}.
$$
Write $D(S)$ for the torus endpoint differences $x-z$ of modular midpoint triples $x,y,z\in S$, including the constant triples. Its Haar measure is well-defined since a projection of a Borel set in these spaces is universally measurable.

**Theorem.** Fix $0<k<K<\infty$. Uniformly as $m\to\infty$ for integer $N$ with $k m^2\le\log N\le K m^2$,
$$
 \sup_{B:\ |D(S_B)|\le1/N}|S_B|
 \asymp_{k,K} A^m m^{-1/2}N^{-1/m}.
$$
At the optimizing dimension $m$ near $\sqrt{\log N/\log(24/7)}$, this includes every union of levels of the canonical energy. The condition is the exact-difference measure budget for the union bound on a random torus direction. The conclusion bounds the Haar average over translates. The full Erdős #142 asks about arbitrary subsets of the integer interval.

The lower estimate follows from the single-interval construction in the companion paper, which puts the entire difference set in an ellipsoid of volume at most $4^{-m}/N$. Its bound for the slice uses only concentration and normalized Haar measure. We prove the upper estimate.

## Interior energies and ordinary chords

Write $l=(2/3)^2$, $u=(17/12)^2$. Fix a small $\delta>0$. For large $m$, all energies between $m(l+\delta)$ and $m(u+\eta^2/4-\delta)$ have the following property. Every value $r$ in that range can be realized as the energy of a midpoint in a positive proportion of directions on an exponential scale. We give two estimates indexed by $b_*=1$ or $b_*=\eta$.

In whitened coordinates $w=(s,\eta t)$ in each block, there is a set $C_{r,b_*}$ of unit directions on the sphere in $\mathbb R^{2m}$ of relative surface measure at least $(c_\delta b_*)^m$. For every $\theta$ in it there is a midpoint $w$ of squared norm $r$, perpendicular to $\theta$, such that $w\pm\sqrt h\,\theta$ are valid representatives in the same polygon as the midpoint in each block whenever
$$
 0\le h\le h_0=c_\delta m\eta^2\quad(b_*=1),\qquad
 0\le h\le h_1=c_\delta m\quad(b_*=\eta).
$$
The difference of these endpoints in the original $(a,b)$ coordinates belongs to $(-1/2,1/2)^{2m}$, so projection of this family of differences to the torus preserves its volume. The energy of each endpoint is exactly $r+h$.

**Construction of the directions.** Use only the high-first-coordinate sheets $T_1,T_2$, on which $(a,b)=(t+1/2,s-t-1/2)$. Pick two fixed interior points, one in each polygon, with squared sums below $l+\delta/2$ and above $u-\delta/2$, respectively. Such points exist by taking $s$ close to $2/3$ and $17/12$; for instance the respective first coordinates may be fixed at $7/12$ and $23/24$. Both have fixed open neighborhoods still in their polygons for all small $e$. Choose multiplicities for the two points so the average whitened squared norm differs from $r/m$ by $O(1/m)$, by rounding the real interpolation weight. Denote these base coordinates by $(s_i,t_i)$.

Use independent standard Gaussian coordinates $(U_i,V_i)$. Within each of the two groups prescribe signs $j_i=\pm1$ with counts differing by at most one. Impose $1\le j_i U_i\le1+\xi$ and $|V_i|\le b_*$ in every block, where $\xi>0$ is a sufficiently small constant depending on the fixed neighborhoods. These events have joint probability at least $(c_\delta b_*)^m$. Their normalized directions form a set of at least this relative surface measure. Set
$$
 z=-\frac{\sum_i (s_iU_i+\eta t_iV_i)}{\sum_i |U_i|}.
$$
Sign balance gives $|z|\le C(\xi+1/m+\eta)$, uniformly in $r$. The vector with physical coordinates $(s_i+zj_i,t_i)$ is perpendicular in whitened coordinates to $(U,V)$. Rescale all its $(s,t)$ coordinates by the same positive factor to give total energy $r$. This factor is $1+O(\xi+1/m+\eta)$ since the starting squared norm per block differs from $r/m$ by at most that order and $r/m$ is bounded below. Both adjustments stay in the chosen neighborhoods if $\xi$ is small enough and $m$ is large.

The norm of the Gaussian vector on this event is between $\sqrt m$ and $3\sqrt m$. In the normalized direction the physical increments in $s,t$ at squared displacement $h$ are bounded by $2\sqrt{h/m}$ and $b_*\sqrt{h/m}/\eta$, respectively. Reducing the common constant in $h_0,h_1$ makes the endpoints stay in their polygons and makes each original coordinate displacement strictly less than $1/4$. The identities for the squared norms follow from perpendicularity. This proves the assertion about directions.

## From chords to the measure of an arbitrary set of levels

Partition the interior energy range into at most $C_\delta$ intervals of length at most $h_1$. In one interval fix any $r\in B$ in that interval. Whenever $r+h\in B$ is in the same interval with $h>0$, the preceding chords supply actual endpoint differences in $D(S_B)$. The map from whitened half-differences to original endpoint differences has absolute determinant $2^{2m}\eta^{-m}$. The unit ball volume is $\omega_{2m}=\pi^m/m!$. In squared radial coordinate $h$, the volume element integrated over the entire sphere is $m\omega_{2m}h^{m-1}\,dh$.

Let $b_s$ be the length of the selected values of $h$ in $(0,h_0]$. Every measurable subset of the positive half-line of length $b_s$ has integral of $m h^{m-1}$ at least $b_s^m$. The directions for $b_*=1$ therefore give
$$
 |D(S_B)|\ge c_\delta^m\eta^{-m}\omega_{2m}b_s^m.
$$
Under the budget we have $b_s\le C_\delta m\eta N^{-1/m}$. Let $b_f$ be the length for $h>h_0$. Using the narrower cone with $b_*=\eta$ cancels the determinant factor $\eta^{-m}$ and gives
$$
 |D(S_B)|\ge c_\delta^m m\omega_{2m}h_0^{m-1}b_f.
$$
Hence $b_f\le C_\delta^m\eta^{-2m+2}/N$. This is $o(m\eta N^{-1/m})$ uniformly since $\eta$ is a fixed positive constant divided by $m$ and $\log N\ge k m^2$. The two lower bounds on the difference set were used separately, so overlap between the cones has no effect. Taking $r$ approaching the infimum of the selected levels in the interval bounds their entire length. Summing over the bounded number of intervals gives
$$
 |B\cap[m(l+\delta),m(u+\eta^2/4-\delta)]|
 \ll_\delta m\eta N^{-1/m}.
$$

## Returning to the probability of a level

Under uniform sampling in $T$, the scalar $G$ has a density bounded by an absolute constant. On each polygon, fix $t$ and integrate in $s$. The derivative of $s^2+\eta^2t^2$ is at least $4/3$. The Jacobian in $(s,t)$ has absolute value one, and $|T|\ge7/36$. The bounded-density sum theorem of Rudelson and Vershynin gives density $O(m^{-1/2})$ for the sum of $m$ independent block energies. The interior probability of selection is therefore $O_\delta(\sqrt m\,\eta N^{-1/m})$.

The endpoints of the scalar range are bounded by $l$ and $u+\eta^2/4$. At either end the probability of lying within $m\delta$ of the corresponding endpoint of the sum is at most $C^m(m\delta)^m/m!\le(Ce_{\rm nat}\delta)^m$, by integrating the bounded joint density over a simplex; here $e_{\rm nat}=\exp(1)$. Choose $\delta$ so this is at most $\exp(-(K+1)m)$. It is then $o(\sqrt m\,\eta N^{-1/m})$. Finally $|T|^m\asymp A^m$ by the EHPS area estimate and $T_e\subset T_0$. Multiplying by this product area proves the theorem.

## Verification and scope

The included rational checks construct chords on both polygon types, verify the representatives and modular midpoints, and compare energies exactly. A separate rational polygon integral gives the limiting mean of $s^2$ as $3515/3024$; the proof covers the full energy range, including its tails. Earlier multiple-annulus constructions for longer progressions use different polynomial conditions. The present obstruction leaves room for other building blocks, other energy functions, restrictions within a level and an exceptional orbit or translate. This is a written proof. Priority and independent review remain open.

1. C. Elsholtz, Z. Hunter, L. Proske and L. Sauermann, *Improving Behrend's construction*, Definition 4.1 and section 3. [arXiv:2406.12290](https://arxiv.org/abs/2406.12290).
2. OpenAI Codex, *A logarithmic refinement for integer sets avoiding three-term progressions*, with the companion single-slice analysis. [Manuscripts](https://github.com/jpollard-cs/open-math-agents/tree/7b07a53de33034c24fc9417f16d42f18ed02c7af/research/proof-manuscripts/erdos142-ellipsoid).
3. M. Rudelson and R. Vershynin, *Small ball probabilities for linear images of high-dimensional distributions*, Theorem 1.2. [Author-hosted paper](https://public.websites.umich.edu/rudelson/papers/rv-smallball.pdf).
4. K. O'Bryant, *Sets of integers that do not contain long arithmetic progressions*. [arXiv:0811.3057](https://arxiv.org/abs/0811.3057).
