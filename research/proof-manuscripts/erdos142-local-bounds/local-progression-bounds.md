# How many positions must a linear inequality see to bound progression-free sets?

*Jordan Pollard, November 27, 2026*

Jordan Pollard directed the research. OpenAI Codex developed the arguments, computed the certificates, and drafted the manuscript.

An upper bound for the largest three-term-progression-free subset of $[N]=\{1,\ldots,N\}$ can be obtained by combining inequalities valid on short lists of positions. The lists can be scattered anywhere in the interval and the coefficients can be arbitrary. We determine the smallest number of positions an inequality must use before this method can force density below one half. The answer is ten. All valid inequalities on at most nine positions together still admit the constant fractional assignment $x_i=1/2$. A single weighted inequality on ten consecutive positions, summed over its translates, gives $\sum x_i\le(10/21)(N+9)$.

## The relaxation and the exact threshold

For a finite set $S$ of integers, let $P(S)$ be the convex hull of the zero-one vectors of its subsets containing no nonconstant three-term arithmetic progression. This polytope is downward closed in the nonnegative orthant. Indeed, each selected element of a random admissible set can be independently discarded with a prescribed probability. Define
$$
 U_L(N)=\max\left\{\sum_{i=1}^N x_i : x|_S\in P(S)
 \text{ for every }S\subseteq[N],\ |S|\le L\right\}.
$$
The variables are real inclusion probabilities. Distributions on different lists are required to agree on the one-point marginals. The relaxation makes no further joint-distribution requirement. The definition includes every valid linear inequality supported on at most $L$ inclusion variables. In particular $r_3(N)\le U_L(N)$.

**Theorem 1.** For each fixed $L$, $U_L(N)=p_L N+O_L(1)$. The exact limiting densities through $L=9$ are
$$
\begin{array}{c|ccccc}
L & 1,2&3,4&5,6&7,8&9\\ \hline
p_L&1&2/3&4/7&1/2&1/2 .
\end{array}
$$
For every $N$, $U_9(N)\ge N/2$, whereas $U_{10}(N)\le(10/21)(N+9)$. In particular $U_{10}(N)<N/2$ for $N>180$. Determining $p_{10}$ exactly is a further question.

**A finite characterization.** For each $S$ let $b(S)$ be the largest $t$ such that the constant vector $t$ belongs to $P(S)$. Linear programming duality gives
$$
 b(S)=\min_{w\ge0,\,\sum_{i\in S}w_i=1}
       \ \max_{A\subseteq S\ \mathrm{progression\text{-}free}}\sum_{i\in A}w_i .
$$
Equivalently a random admissible subset must include each point with probability at least $t$; downward closure can equalize its marginals. This also identifies $1/b(S)$ with the fractional chromatic number of the hypergraph of progressions on $S$.

Take $p_L=\min_{|S|=L} b(S)$ over integer sets. The minimum exists since only finitely many ordered triple patterns are possible. Extending a smaller set to $L$ positions shows that the same minimum works for all sizes up to $L$. Thus $x_i=p_L$ is feasible on every interval. Translate an attaining set into $[0,D]$ and let $w$ be its optimal weights. Extend any feasible $x$ by zero outside $[N]$. The weighted constraint on every translated list remains valid even at a boundary, because the distribution on its intersection with $[N]$ can be extended by the empty choice elsewhere. Sum the constraints over translations $1-D,\ldots,N$. Each coordinate is counted with total weight one, hence $U_L(N)\le p_L(N+D)$. This proves the limit statement.

**Explicit upper certificates.** The ordered lists below have the indicated nonnegative integer weights. The final column gives the largest weight of any progression-free subset; it can be checked by inspecting at most $2^{10}$ subsets.
$$
\begin{array}{c|l|l|c}
 |S|&S&w&\max w(A)/w(S)\\ \hline
 3&0,1,2&1,1,1&2/3\\
 5&0,2,3,4,6&1,2,1,2,1&4/7\\
 7&0,2,3,4,5,6,8&1,1,1,2,1,1,1&4/8\\
 10&0,1,2,3,4,5,6,7,8,9&2,3,4,5,5,6,5,5,4,3&20/42
\end{array}
$$
Monotonicity gives the intervening upper bounds. The ten-point list has diameter nine.

## Why the lower certificates cover arbitrary integer placements

Write the points in increasing order and let $g_1,\ldots,g_{s-1}>0$ be their consecutive gaps. Each prospective midpoint relation is a homogeneous linear equation in the gaps: two sums of adjacent runs of gaps must be equal. Adding midpoint relations can only decrease $b(S)$.

For $3\le s\le6$ the verifier enumerates an extension of every possible pattern. Given any realizable midpoint equations, rescale to impose $g_i\ge1$ and minimize $\sum g_i$. The minimizing face is nonempty and bounded, and has a vertex. At that vertex $s-1$ independent equations come from the midpoint equations and the constraints $g_i=1$. The verifier enumerates all such bases by exact integer elimination. Each resulting positive rational gap vector can be scaled back to integers. Each original pattern is contained in one of those enumerated, and contained patterns can be removed from the list. For sizes 3, 4, 5, 6 the respective numbers of inclusion-maximal ordered patterns are 1, 3, 16, 152. For each, the data supply a rational distribution on admissible subsets with every marginal at least the corresponding value in Theorem 1. The verifier sums the fractions exactly. It also checks dual weight certificates by testing every admissible subset.

For sizes up to nine the target lower bound is $1/2$ once $s\ge7$. A two-coloring without a monochromatic progression gives the desired marginals by choosing one color uniformly. The known value $W^*(3)=9$ already implies such a coloring for every eight-point set, while nine-point sets may require three colors. To treat nine positions we enumerate only the patterns for which this coloring argument fails. This part is needed even for the nine consecutive integers. [Eric Tressler, *Integral and Euclidean Ramsey Theory*, Proposition 6](https://escholarship.org/uc/item/7kc6d61j)

Begin with the cone of nonnegative gap vectors and its coordinate rays. At each node we have imposed some midpoint equations and consider strictly positive gaps in that cone. For a prospective new equation evaluate its left side on the generating rays. If all values vanish then the equation is forced. If both signs occur, the equation can cut the relative interior. When the values have one sign and include a nonzero value, the equation is impossible for strictly positive gaps: a strictly positive point in this nullspace cone is in its relative interior.

Choose a two-coloring avoiding all currently forced monochromatic triples, if one exists. Any uncolorable completion must make some monochromatic triple of this coloring into an actual progression. Recurse once for each such equation of mixed signs. If no coloring is available, record the forced pattern and recurse on every mixed-sign equation to cover its strict extensions. The dimension drops at every branch. A generic interior point has exactly the forced relations, since a finite union of proper hyperplanes cannot cover the relative interior; it can be chosen rational.

To intersect the cone with a new equation, keep its zero rays. For every pair with evaluations $a>0$ and $-b<0$, add the ray $b u+a v$. These rays generate the intersection: in a nonnegative combination of old rays with total evaluation zero, the positive and negative contributions can be matched in equal portions. Primitive rays of minimal support suffice. In the intersection of a linear subspace with the nonnegative orthant, an extreme ray cannot properly contain the support of another ray, since a small multiple of the latter can be subtracted. Two independent rays with the same support likewise give a decomposition by perturbing until a coordinate vanishes. These observations justify both the exact arithmetic and the pruning in the verifier.

The search visits 22,805 distinct cones and returns 24 ordered nine-point patterns without a valid two-coloring. Rational distributions on progression-free subsets certify a minimum marginal of at least $1/2$ for all 24. Nineteen have $b(S)=1/2$, two have $b(S)=10/19$, two have $b(S)=18/35$ and one has $b(S)=12/23$. Colorings or these rational distributions therefore cover every nine-point set, and restriction handles all smaller sizes. Together with the three-through-six computations and the explicit upper certificates, this proves Theorem 1.

## How the obstruction grows with the number of positions

**Theorem 2.** For $L\ge2$,
$$
 \frac{r_3(L)}{5L-3}\ \le\ p_L\ \le\ \frac{r_3(L)}{L}.
$$
Consequently if $\log L=o((\log N)^{2/9})$ with $2\le L\le N$, then $U_L(N)/r_3(N)\to\infty$. The bound concerns linear constraints on the original inclusion variables; it gives no restriction on arguments using additional variables for pairs or higher correlations.

The upper comparison uses the list $[L]$ with equal weights. For the lower comparison we adapt Ruzsa's random affine projection proof of the Komlós--Sulyok--Szemerédi transfer theorem, keeping track of each point's individual marginal. Let $B\subseteq\{0,\ldots,L-1\}$ be a largest progression-free set, $Q=2L-1$, and $w=1/(2Q)$. Center a half-open arc of length $w$ at $b/Q$ on the circle for each $b\in B$. Map a list of $s\le L$ integers to the circle by $x\mapsto \alpha x+\beta\pmod1$, with $\alpha,\beta$ independent and uniform. From each occupied arc pick one list element uniformly.

The chosen integers have no nonconstant three-term progression. For a progression their images satisfy the midpoint equation modulo one. After scaling by $Q$, the three center labels satisfy it modulo $Q$, since the sum of the signed rounding errors has absolute value strictly less than one. The centers are represented between zero and $L-1$, so the congruence is an equality. The defining property of $B$ forces a common label, whereas the sampling rule takes only one point per arc.

For distinct integers $x,y$ their phases are independent uniform points: the integer matrix of the two phases has nonzero determinant and defines a surjective homomorphism of the two-dimensional torus. Conditioned on $x$ landing in a specified arc, the expected occupancy is $1+(s-1)w$. Convexity of the reciprocal gives conditional survival probability at least $1/(1+(s-1)w)$. Summing over the arcs yields the marginal bound $|B|/(4L-2+s-1)\ge r_3(L)/(5L-3)$.

Finally, Behrend's construction gives $r_3(L)/L\ge c\exp(-C\sqrt{\log L})$, while Bloom and Sisask give $r_3(N)/N\le\exp(-c'(\log N)^{1/9})$ for sufficiently large $N$. Combining these estimates with $U_L(N)\ge Np_L$ proves the stated divergence. The argument explains why optimizing all small-position inequalities cannot by itself find the unrestricted order of magnitude in Erdős #142. We do not establish that order here. [Ruzsa, Theorem 4.4](https://matwbn.icm.edu.pl/ksiazki/aa/aa72/aa7248.pdf), [Behrend-type lower bounds](https://doi.org/10.48550/arXiv.2406.12290), [Bloom and Sisask](https://arxiv.org/abs/2309.02353), [Erdős #142](https://www.erdosproblems.com/142)

## Reproducing the finite proof

The accompanying Python checker and C++17 template enumerator verify the rational certificates without an optimization library. Run `python check.py` with Python 3.10 or later and a C++17 compiler. The optional `--generate` flag uses SciPy to propose fresh certificates and then subjects them to the same exact checks. The general arguments are written proofs, and the finite classifications have executable certificates. We have not established priority for the local linear-programming thresholds.
