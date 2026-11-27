# A logarithmic refinement for integer sets avoiding three-term progressions

OpenAI Codex, prepared for Jordan Pollard, 27 November 2026  
AI-generated research manuscript for public review. All logarithms are natural.

Let $r_3(N)$ be the largest size of a subset of $\{1,\ldots,N\}$ containing no three distinct integers in arithmetic progression.

**Theorem 1.** There is an absolute $c>0$ such that for every integer $N\ge 3$,
$$
r_3(N)\ge c\,N(\log N)^{-1/4}
\exp\!\left(-2\sqrt{\log(24/7)\,\log N}\right).
$$
The last display in section 3 of Elsholtz, Hunter, Proske and Sauermann (EHPS) gives the same exponential with prefactor $(\log N)^{-3/2}$. Theorem 1 gains a factor of $(\log N)^{5/4}$ in this comparison. EHPS supply the block and the leading constant. The random torus map, spherical volume and concentration arguments have precedents in Green and Wolf's treatment of Elkin's refinement. The extra ingredient here is the volume of an ellipsoid with a distinguished direction in every two-dimensional block. Theorem 2 below determines exactly the leading curvature cost in the natural two-parameter family of potentials on this block.

## 1. A directional midpoint inequality

Write $A=7/24$, $s(x)=x_1+x_2$, and use representatives in $[0,1)^2$. EHPS Proposition 2.2 and Lemma 4.4 give, for $0<\epsilon<1$, their explicit set $T=T_\epsilon$ of area at least $A-\epsilon$ and a measurable $0\le f\le 100\epsilon^{-2}$ with the following properties. For every $x,y,z\in T$ with $x+z\equiv 2y\pmod 1$,
$$
 f(x)+f(z)-2f(y)\ge |x-z|^2,\qquad
 s(y)\le \tfrac12(s(x)+s(z)).
$$
The first inequality uses Euclidean distance between the representatives. Because $s$ is nonnegative, the second inequality gives
$$
 s(x)^2+s(z)^2-2s(y)^2\ge \tfrac12(s(x)-s(z))^2.
$$
Consequently $H=f+2\epsilon^{-2}s^2$ takes values in $[0,108\epsilon^{-2}]$ and satisfies
$$
 H(x)+H(z)-2H(y)\ge Q(x-z),\qquad
 Q(u)=u_1^2+u_2^2+\epsilon^{-2}(u_1+u_2)^2.
$$
The two orthogonal directions $(1,-1),(1,1)$ have eigenvalues $1,K$, with $K=1+2\epsilon^{-2}$.

## 2. A slice in the product and a line on the torus

Fix $d=2m\ge2$ and set $\epsilon=A/d$. Under independent uniform sampling from $T$ in each block, the sum $F=\sum_{i=1}^m H(x_i)$ has variance at most $m(108\epsilon^{-2})^2$. Chebyshev's inequality places at least three quarters of this probability in an interval of length $432\sqrt m\,\epsilon^{-2}$. Partitioning that interval into pieces of length at most $\Delta$ gives a measurable slice $S\subset T^m$ where $F$ lies in one interval of width $\Delta$ and
$$
 |S|\gg (A-\epsilon)^m\min\{1,\Delta\epsilon^2/\sqrt d\}.
$$
Here and below the implicit constants are absolute. In any modular midpoint triple in $S$, the endpoint difference in the chosen representatives belongs to
$$
 E=\{u\in\mathbb R^d:\ \textstyle\sum_{i=1}^m Q(u_i)\le 2\Delta\}.
$$
Indeed the sum of the midpoint inequalities is bounded above by twice the width of the slice.

The measure of the image of $E$ in the torus is at most its Euclidean volume, by partitioning into translates of the unit cube. The change of variables that multiplies the sum direction by $\sqrt K$ in each block gives
$$
 |E|=\frac{\pi^m(2\Delta)^m}{m!K^{m/2}}
 \le \left(\frac{4\pi e\Delta}{d\sqrt K}\right)^m.
$$
Set $\Delta=d\sqrt K\,N^{-2/d}/(16\pi e)$. If $b$ is uniform on the torus, each $j b$ with $1\le j\le N$ is uniform. A union bound gives probability at most $4^{-m}$ that any of these points lies in the image of $E$. Fix a $b$ avoiding this event. For any translate $a$, the set of indices $1\le j\le N$ with $a+jb\in S$ is progression-free. Indeed, a progression of indices $i<j<k$ would produce a modular midpoint triple and place $(k-i)b$ in the image of $E$. Averaging over uniform $a$ gives at least $N|S|$ indices for some translate.

Now $(A-\epsilon)^m=A^m(1-1/d)^{d/2}\ge A^m/2$, and $\Delta\epsilon^2/\sqrt d\asymp d^{-1/2}N^{-2/d}$. The latter expression is bounded by one. Uniformly for even $d\ge2$ and $N\ge3$ this proves
$$
 r_3(N)\gg N d^{-1/2} (7/24)^{d/2} N^{-2/d}.
$$
Set $L=\log N$ and $a_0=\log(24/7)$. The quantity $a_0d/2+2L/d$ is minimized at $d_*=2\sqrt{L/a_0}$. Rounding to the nearest positive even integer costs at most $a_0(d-d_*)^2/(2d)$ in the exponent, by the exact identity for the difference from the minimum. Since $d^{-1/2}\asymp L^{-1/4}$, this proves Theorem 1 after absorbing small $N$ into the constant.

## 3. Sharp stiffness in the quadratic family

Put $g(t)=t^2$ for $0\le t<1/2$ and $g(t)=(t-1/2)^2$ for $1/2\le t<1$. Let $C_\beta(\epsilon)$ be the infimum of $C\ge0$ such that the potential $C s^2+\beta g(x_1)$ has midpoint gap at least $|x-z|^2$ for every modular midpoint triple in $T_\epsilon$. An empty infimum is $+\infty$.

**Theorem 2.** For each fixed $\beta>4$,
$$
 C_\beta(\epsilon)=\left(1+\frac{3\beta}{4}\right)\epsilon^{-2}
                       +O_\beta(\epsilon^{-1})\qquad(\epsilon\downarrow0).
$$
For $\beta\le4$ this curvature is infinite. Thus the leading coefficient is $11/2$ for the EHPS choice $\beta=6$. This sharpness statement concerns the specified potential family.

**Upper bound.** EHPS Lemma 4.4 gives $s(y)=\tfrac12(s(x)+s(z))$ or a downward shift from that average by $1/2$. In the shifted case the gap in $s^2$ is at least $1/2$, so $C\ge4+\beta$ suffices. In the other case put $v=s(x)-s(z)$ and $u=x_1-z_1$. The gap in $s^2$ is $v^2/2$, and $|x-z|^2=2u^2-2uv+v^2$. Since $y_1$ agrees with $(x_1+z_1)/2$ modulo $1/2$, their values of the half-periodic $g$ agree.

If both first coordinates are below $1/2$, or their sum is at least one, the gap in $g$ is at least $u^2/2$. In the first case this is the quadratic identity. In the second, use $g(t)\ge(t-1/2)^2$ on the block (EHPS Fact 4.3(ii)) and the quadratic identity at the midpoint. With $B=\beta/2-2>0$, the inequality $2|uv|\le Bu^2+v^2/B$ shows that $C\ge 2(1+1/B)$ suffices.

The remaining case has first coordinates $h\ge1/2$ and $l<1/2$ with $h+l<1$. Order the endpoints so $x_1=h$ and $z_1=l$, and write $u=h-l$. EHPS Lemma 4.6 forces $|v|\ge\epsilon$. Definition 4.1 gives $l>1/4$ and hence $h<3/4$. Here
$$
 g(h)+g(l)-2g(y_1)=u^2/2-h+1/4.
$$
The deficit before adding the $s^2$ term is
$$
 D=(2-\beta/2)u^2+\beta(h-1/4)-2uv+v^2.
$$
Since $u\ge2h-1$, the first two terms are bounded by
$(2-\beta/2)(2h-1)^2+\beta(h-1/4)$. This function has derivative at least $4$ on $[1/2,3/4]$ and value $1/2+3\beta/8$ at its right endpoint. Also $u\le1/2$. Thus
$$
 2D/v^2\le (1+3\beta/4)\epsilon^{-2}+2\epsilon^{-1}+2.
$$
This covers every triple.

**Lower bound.** For $0<e=\epsilon\le1/100$ take the following representatives and their ordinary midpoint:
$$
 x=(3/4-2e,\ 1/2-e^2),\qquad
 z=(1/4+2e-e^2,\ 1-3e+2e^2),\qquad y=(x+z)/2.
$$
All three sums lie between $7/6+e$ and $17/12$. The point $x$ is in EHPS region $T_2$. Both $z$ and $y$ lie in $T_3$, with $2z_1+z_2=3/2+e$ and $2y_1+y_2=7/4-3e/2-e^2/2$. Moreover $x_1+z_1=1-e^2$ and $v=-e-2e^2$. Thus $h=3/4+O(e)$, $u=1/2+O(e)$, and the displayed deficit is $1/2+3\beta/8+O_\beta(e)$. This triple demands $C\ge2D/v^2$, giving the claimed lower bound.

Finally the interior of $T_1$ contains an open ball with first coordinate above $1/2$. Choose an interior midpoint and take symmetric endpoints in that ball with fixed small first-coordinate difference $u>0$ and second-coordinate difference $v-u$. There the gap in $g$ is $u^2/2$ and the gap in $s^2$ is $v^2/2$. At $v=0$ the required inequality forces $\beta\ge4$. At $\beta=4$ and $v<0$ tending to zero it forces $C\ge 2-4u/v$. No finite $C$ works in that case.

## 4. A graph construction and verification

Let $M=2N+1$. On two labeled copies of $\mathbb Z/M\mathbb Z$, for each residue $y$ join $y-a$ on the left to $y+a$ on the right for each $a$ in any progression-free set $P\subseteq[1,N]$. This cyclic form of the Ruzsa–Szemerédi construction gives exactly $M$ pairwise edge-disjoint induced matchings of size $|P|$ on $2M$ vertices. The endpoint sum determines $y$ since $M$ is odd. A cross-edge between the vertices indexed by $a,b\in P$ within one matching would require $a+b\equiv2c\pmod M$ for some $c\in P$. Both sides lie in $[2,2N]$, forcing equality and $a=b=c$. Applying Theorem 1 gives the corresponding size guarantee for each matching.

The Python checks supplied with this note exhaust 1,589,533 ordered modular triples on grids of denominators 24, 36, 48, 60 and 84, including 314,130 with coordinate wrap. They check the directional inequality using integer arithmetic. A separate rational computation checks the lower-bound family in Theorem 2. The general results above have written proofs. Priority and independent peer review remain open.

The gap to the unrestricted order of magnitude in Erdős #142 remains large. The upper bound in Raghavan's 2026 preprint has exponential saving of order $(\log N)^{1/6}/\log\log N$. Increasing the area of the two-dimensional block beyond $7/24$, or finding a different upper-bound argument, remains a separate task. Theorem 2 identifies what simply adjusting the two quadratic coefficients can achieve.

## References

1. C. Elsholtz, Z. Hunter, L. Proske and L. Sauermann, *Improving Behrend's construction: Sets without arithmetic progressions in integers and over finite fields*, especially Proposition 2.2, section 3 and Lemmas 4.4 and 4.6. [arXiv:2406.12290](https://arxiv.org/abs/2406.12290).
2. B. Green and J. Wolf, *A note on Elkin's improvement of Behrend's construction*. [Oxford Research Archive](https://ora.ox.ac.uk/objects/uuid:5bc7d654-9814-49f7-97bc-9ec4ac373138).
3. Z. Hunter, *New lower bounds for $r_3(N)$*, Proposition 1.3 and Remark 1.1. [arXiv:2401.16106](https://arxiv.org/abs/2401.16106).
4. R. Raghavan, *Improved Bounds for 3-Progressions*. [arXiv:2603.27045](https://arxiv.org/abs/2603.27045).
5. N. Alon, A. Moitra and B. Sudakov, *Nearly complete graphs decomposable into large induced matchings and their applications*, introduction on the Ruzsa–Szemerédi construction. [Author-hosted paper](https://web.math.princeton.edu/~nalon/PDFS/inducedmatch13.pdf).
