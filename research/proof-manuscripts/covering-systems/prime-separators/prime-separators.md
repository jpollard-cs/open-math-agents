# How many shared primes does an irreducible covering set need?

Codex (OpenAI), at Jordan Pollard’s request, 27 November 2026. Written proof for review.

Let A be an irreducible covering set of k distinct integers greater than one. Removing even one modulus must destroy coverability under *all* reassignments of residues. Put M=max A and S(A)=Σ 1/n. Let τ(A) be the minimum number of primes whose removal leaves each member of A with at most one **distinct** prime factor. Equivalently this is the vertex-cover number of the graph joining primes that divide the same modulus. All occurrences of a removed prime, including its powers, are ignored. These edges use the actual moduli. The earlier sparse-label paper allows one to replace a modulus by a chosen divisor when forming its graph; the two restrictions differ.

Throughout, log is natural. Three results concern both optimization problems in Erdős #1189.

1. For fixed α>1, under M≤X and τ(A)≤(log X)^α, the largest achievable cardinality is
   $$
   X^{(2\alpha-2)/(2\alpha-1)+o(1)}.
   $$
   Every sufficiently large exact cardinality is realized with the inverse exponent. For 0<α≤1 the largest cardinality is X^{o(1)}. In particular, no fixed power of log M shared primes suffices for a family with M=k^{1+o(1)}.
2. With at most a fixed number r≥1 of shared primes, the minimum largest modulus at every sufficiently large exact size k satisfies
   $$
   \log M_r(k)\asymp_r k^{1/(2r+1)}(\log k)^{2/(2r+1)}.
   $$
   The first r primes suffice for the upper construction.
3. At every sufficiently large exact size k, the largest reciprocal sum among covers with τ(A)≤(log k)^α, for fixed α>0, is
   $$
   (e^\gamma\alpha+o(1))(\log\log k)^2 .
   $$
   With r fixed, the corresponding maximum is asymptotic to
   $$
   \prod_{i=1}^{r}(1-1/p_i)^{-1}\log\log k ,
   $$
   where the p_i are the first primes. A separate unconditional bound below forces a **polynomial** number of shared primes in every family attaining reciprocal mass at least c log k for fixed c>0.

The unrestricted minimum and sharp unrestricted reciprocal coefficient remain open. In particular these theorems impose a condition on the prime factors of the modulus set, not on the choice of residues.

## 1. The cap upper bounds

Fix a vertex cover H with at most r primes. Let D_H(t) count positive H-smooth integers up to t, including 1. Outside H each modulus is uniquely p^j d, j≥1, d supported on H. Suppose p^b exactly divides the period lcm(A). In any covering assignment choose a point missed by the rows omitting p^b. Such a point exists by irreducibility. Vary the highest base-p digit, leaving the other coordinates fixed. Each of the p possible values requires a different row divisible by p^b. Those rows have distinct cofactors d, so
$$
 p\le D_H(X/p^b)\le D_H(X/p).
\tag{1}
$$
This uses the full irreducibility hypothesis and distinct moduli; it also implies p≤k.

Replacing the primes in H, in increasing order, by the first r primes can only increase D_H(t). First put r≤(log X)^α. For 0<s<1, Rankin’s bound gives
$$
 D_H(t)\le t^s\prod_{h\in H}(1-h^{-s})^{-1}.
$$
The logarithm of the product is O_s(1+r^{1-s}) by comparison with the first r+1 integers. For every fixed s>max(0,1−1/α) this is o(log X), uniformly in H. By (1) all exterior primes satisfy p≤X^{s/(1+s)+o(1)}. Sum D_H(X/p^j) over these primes and over j≤log X/log 2, bounding each by D_H(X/p). The sum over p of p^{-s} is O_s(P^{1-s}) up to P, even when all integers are allowed. Including pure H-rows gives
$$
 k\le X^{2s/(1+s)+o(1)}.
$$
Let s decrease to max(0,1−1/α). This proves the first upper exponent, including its zero range.

For fixed r write x=log X. There are O_r((1+x)^r) possible hub products, by counting exponent vectors. Thus (1) gives p≤C_r x^r. The count of all permitted rows is at most
$$
 O_r\left(x^r+x^{r+1}\sum_{p\le C_r x^r}\frac1{\log p}\right)
 =O_r\big(x^{2r+1}/(\log x)^2\big).
$$
The prime sum estimate follows from Chebyshev's bound by splitting at the square root of its upper endpoint.

## 2. Parallel prime branches that stay essential

We use the previously proved substitution principle with **indexed** rows; equal virtual moduli are permitted. If an old indispensable row has modulus d and an irreducible indexed packet on a fresh coprime period has moduli b_i, replace it by e_i b_i where e_i divide d and lcm(e_i)=d. All new rows remain indispensable under arbitrary reassignment. Indeed the remaining old rows leave holes. Over each hole the inner coordinates can vary freely, so all packet indices must be present and active there. The old holes then lie in a single class modulo d. Contracting back forces every old row. Conversely align the cofactor residues to the old class and use a covering assignment of the packet. This argument also shows that successive packets may use the same cofactor pool. [Earlier substitution proof and Lean source](../sparse-labels/IntegerSubstitution.lean)

Construct an old system with one distinguished row of modulus Q supported on the first r primes. Write Q as the product of their prescribed full powers. At the stage h^a use the indexed packet with h−1 copies of h^j for each 1≤j≤a, and one additional distinguished h^a. It partitions the h^a residue classes by first nonzero digit and a final zero. Its reciprocal mass is one, so every deletion fails under any reassignment. For each j dress its h−1 ordinary rows with distinct divisors of the preceding core, and dress the distinguished one with the full preceding core. Start with a virtual row 1. The result has precisely b(Q)=Σ a(h−1) ordinary rows plus the distinguished Q. Ordinary rows are distinct by their newest prime and exponent. A temporary equality with the distinguished row is harmless.

For consecutive seed primes there are enough divisors even with each preceding exponent one: for the ith prime Bertrand's postulate gives p_i−1≤2^{i−1}. When r grows, the h−1 divisors can all be chosen O(h), with an absolute implicit constant. Indeed the squarefree integers up to 4h have cardinality >2h for large h, while only O(h/log h) have a prime factor ≥h (write each as a bounded integer times such a prime). Each remaining squarefree integer divides the earlier primorial. Enlarge the constant for the finitely many small primes.

Here is the simultaneous branching step. For any integer t≥1 turn the single row Q into t virtual rows in a balanced binary subdivision of its residue class, with moduli Q times powers of two ≤2t. Take 2^j≤t<2^{j+1}, first split to depth j and split t−2^j more of those leaves once. The old period is Q and 2 divides Q. The resulting indexed system is irreducible under reassignment. One must justify this even though sibling subdivisions may share a higher binary digit. In an arbitrary assignment the ordinary rows still leave at least one entire Q-class uncovered. The new rows have total density exactly 1/Q. A deletion of a new row cannot fill even one missing Q-class. If they are all present, their union can fill at most one such missing class. Thus every ordinary hole lies in a single Q-class and contraction forces all ordinary rows. This proof works for any t, including t=1.

Assign a different fresh prime p to each leaf d. Replace this leaf using the preceding p-adic packet with exponent b≥1. Choose p−1 distinct divisors of d at each ordinary p-power and p distinct divisors at the terminal power; here the terminal p entries include the additional distinguished entry and terminate the branch. Across the packet ensure lcm of the chosen divisors is d, for instance by including its full hub prime powers. There are 1+(p−1)b rows on this branch. All final moduli are distinct, by their unique exterior prime and its exponent, and distinct cofactors within an exponent. Every old ordinary row, and every row in every branch, is indispensable by applying the substitution principle one fresh prime at a time. The final cardinality is exactly
$$
 b(Q)+\sum_{p\ {\rm selected}}(1+(p-1)b_p).
\tag{2}
$$
The binary refinement is what permits the same hub primes to support many independent branches without requiring a modulus to contain two exterior primes.

## 3. Polynomially many logarithmic primes

Fix α>1, let y=(log X)^α, and take as H the primes through y. Put Q=lcm(1,…,⌊y⌋), permitting one optional extra exponent at each prime. The number of hubs is at most (log X)^α. The seed ordinary moduli are O(y^3), by the divisor estimate above. Its ordinary row count before optional exponents is at most O(y² log y). Optional exponents vary that count over a complete integer interval from its baseline to baseline+Σ_{h≤y}(h−1). The increments 1,2,4,6,… have complete subset sums, since Bertrand ensures each next increment is at most one plus the previous total. The interval has length much greater than y.

Let w=1−1/α and choose a fixed 0<θ<w/(1+w). Write P=X^θ. Use exterior primes in (y,P], with b_p=1. There are enough divisors of Q up to X/P for even the last branch. Indeed every product of j=⌊log(X/P)/log y⌋ distinct primes through y is such a divisor. The logarithm of their number, by the prime number theorem and the elementary binomial bound (n/j)^j, is at least
$$
 ((1-\theta)(1-1/\alpha)+o(1))\log X>\log P .
$$
All full powers in a leaf are ≤2y²P, since there are at most P leaves and the optional extra exponent costs a factor ≤y. This is below X/P eventually because θ<1/2. A leaf requires at most π(y) mandatory full powers, and p>y. Fill its p slots with distinct divisors ≤X/P including those mandatory powers. Every resulting modulus is ≤X.

Selecting an exterior prime adds exactly p to (2). Once an interval of seed choices has length at least the next prime minus one, taking that prime or skipping it produces a longer complete interval. The seed interval covers the gap to the first outside prime, and Bertrand keeps the condition valid thereafter. One may require the first prime unconditionally to keep the number of leaves positive. Thus every cardinality from a polylogarithmic baseline through Σ_{y<p≤P}p+O(polylog X) occurs under the cap. The upper endpoint is X^{2θ+o(1)}. This proves sharpness of the exponent and all-size inversion: for each sufficiently large k and any fixed η>0 one may take cap X=k^{1/d+η}, d=2w/(1+w). The baseline is smaller than k and the upper endpoint exceeds k for a suitable fixed θ. Shrinking η gives the inverse exponent, with the hub budget measured at the allowed cap X.

## 4. A fixed number of hub primes

Let x=log X and H be the first r primes. Give each hub exponent ⌊c_r x⌋, where c_r>0 is small enough that Q≤e^{x/4} even when the exponent of 2 is varied from ⌊c_r x⌋ to 2⌊c_r x⌋. There are at least c'_r x^r divisors of Q. Use all or any subset of the primes h_r<p≤P=c''_r x^r with c''_r sufficiently small. Each selected p permits any b from 1 to ⌊x/(2 log p)⌋. Every divisor used is ≤2PQ≤e^{x/2} for large x. All mandatory powers fit in p slots and there are at least p divisors. Thus all final moduli are ≤X.

Varying the binary exponent gives an interval of seed cardinalities of length asymptotic to c_r x. Require the smallest exterior prime at b=1. Each subsequent p contributes one of 0,p,2p−1,…,1+(p−1)⌊x/(2 log p)⌋. The gaps are at most p. Once the current interval has length ≥p−1 its sum with this list is again an interval, long enough for the next prime by Bertrand and the available last entry. The largest cardinality is at least a constant times xP²/(log P)^2, counting just primes P/2<p≤P and using the prime number theorem. The baseline is O_r(x), so inversion gives assertion 2 at every sufficiently large k.

## 5. The reciprocal coefficient for logarithmically many hubs

All hub-only rows have total reciprocal ≤V_H=∏_{h∈H}(1−1/h)^{-1}. Exterior rows contribute in total at most V_H Σ_{p≤k,p∉H}1/(p−1), counting all prime powers. Here p≤k follows from (1), or directly from the highest base-p digit. If |H|≤(log k)^α, Mertens' product estimate and the prime number theorem bound V_H≤(e^γ α+o(1)) log log k. Mertens' prime sum gives Σ_{p≤k}1/(p−1)=log log k+O(1). For r fixed the first r primes give the largest V_H.

In fact write r=r(k)≥1 with r=k^{o(1)}, y=p_r, and V_r=∏_{i≤r}(1−1/p_i)^{-1}. If R_r(k) denotes the restricted maximum, the sharper joint formula is

$$
 R_r(k)\sim V_r\log\left(\frac{\log k}{\log y}\right).
$$

The interchange argument in section 6, applied to all primes ≤k, bounds the sum above by V_r(1+Σ_{y<p≤k}1/(p−1)). The prime sum differs from log(log k/log y) by O(1), uniformly in y. This logarithm tends to infinity.

For the lower bound take H to be the primes through y and Q initially lcm(1,…,y). If r remains bounded, instead use exponent at least ⌈log log k⌉ for each of these primes so the reciprocal weight of the divisors approaches the full Euler product. Uniformly one can achieve the same effect by taking Q=lcm(1,…,y) multiplied by the product of the first r primes each to the power ⌈log log k⌉. Increase the exponent of 2 by another ⌈5√(k log k)⌉. This provides more than 4√(k log k) distinct divisors even if r=1, while the ordinary seed still costs o(k) rows because y=k^{o(1)}. Allow an additional variation of the binary exponent through an interval of length ⌈3k^{1/8}⌉, at cost o(k). No cap is imposed on M in the reciprocal problem.

Put B=k^{1/8}. Require every prime y<p≤B as a branch at exponent one. These branches cost O(B²). Additionally allow primes B<p≤4√(k log k) as optional branches. The seed interval bridges the first optional prime. Successive optional weights give complete interval sums by Bertrand, and their total exceeds k by the prime number theorem. The mandatory baseline is o(k). Formula (2) therefore gives any prescribed sufficiently large k.

In a required branch include each full hub power of the leaf to ensure the cofactor lcm. Also include all divisors d of Q with d≤p/2 when p≥2r+2, filling the p slots with arbitrary remaining distinct divisors. Set T=log k/log y and L=exp(√(log T)). For y^L≤p≤B the small divisors carry (1−o(1))V_r, uniformly. Under reciprocal weights on all H-smooth integers, normalized by V_r, the mean of log d is Σ_{h≤y}log h/(h−1)=O(log(2y)). Markov's inequality bounds the relative weight of d>p/2 by O(1/L). The relative weight of d failing to divide Q tends to zero: the exponents are at least ⌈log log k⌉, so a union bound gives at most Σ_{n≥2}n^{−⌈log log k⌉−1}=o(1). The prime sum over this range is log T−log L+O(1)=(1−o(1))log T. Also y^L=k^{o(1)} and y^L≥2r+2 eventually. This proves the joint formula, both forms of assertion 3, and attainment at every exact size.

## 6. A consequence for unrestricted covers

The period inequality of Znám and Simpson gives Σ_{p|lcm(A)}(p−1)≤k−1. Thus the active primes above Y=√(k log k) have total Σ1/(p−1)=O(1/log k). Removing them from the Euler product for the hubs and from the exterior sum changes our upper bound by o(log k): the active Euler product is O(log k), and the complete expression is O(log k), since (1+Σ a_p)≤∏(1+a_p) for a_p≥0.

On primes ≤Y the expression V_H(1+Σ_{p∉H}1/(p−1)) is maximized at fixed hub budget by putting the smallest primes in H. Adding a hub weakly increases the expression. To interchange a smaller exterior prime and a larger hub prime, write a>b for their respective reciprocal increments 1/(p−1) and T for the exterior sum excluding a. After factoring out the common product, the gain is (a−b)T≥0. We may freely include all primes ≤Y in this upper estimate. If r=k^{δ+o(1)}, 0<δ<1/2, the last of the first r primes has logarithm (δ+o(1))log k. The resulting bound is
$$
 \limsup S(A)/\log k\le e^\gamma\delta\left[1+\log(1/(2\delta))\right].
$$
For r=k^{o(1)}, first bound r by k^δ for arbitrary fixed δ and then send δ to zero. In particular even the attained coefficient 1/2 requires a polynomial number of shared primes in the actual modulus graph. For c=1/2 the equation on the right gives δ≈0.112780841. Thus any family with S(A)≥(1/2−o(1))log k requires τ(A)≥k^{0.11278084−o(1)}. This is a necessary condition; the sharp unrestricted coefficient remains undetermined.

## 7. A stronger necessary condition near the unrestricted cap

Write log₂ X and log₃ X here for iterated natural logarithms. If irreducible sets with cap X have k≥X/(log X)^{a+o(1)} for fixed a>0, their minimum vertex-cover number satisfies

$$
 \log(2+\tau(A))\ge
 \left(\frac1{2a}-o(1)\right)
 \frac{\log X\,\log_3 X}{\log_2 X}.
$$

In particular a family with M=O(k log k) requires the coefficient 1/2 on the right at X=M. To prove this, suppose the hub count were at most exp(c log X log₃ X/log₂ X) along a sequence, for some c<1/(2a). The primes in the hub can be compressed to the first primes when counting their products. All compressed primes are ≤y=exp(c′ log X log₃ X/log₂ X) for any fixed c<c′<1/(2a), eventually, by the prime number theorem.

Every exterior prime p is ≤√X since the highest base-p digit needs p distinct multiples of p. For exterior powers p^j≤√X, the remaining cofactor is counted by Ψ(X/p^j,y), the count of y-smooth integers. Uniformly for √X≤z≤X, Hildebrand’s estimate Ψ(z,y)∼zρ(log z/log y), with ρ decreasing, and log ρ(u)∼−u log u give
$$
 \Psi(z,y)\le z(\log X)^{-1/(2c')+o(1)}.
$$
Indeed log(√X)/log y=log₂ X/(2c′log₃ X). Summing reciprocals of the powers p^j costs O(log log X), including the pure-hub term. For the remaining powers j≥2 with p^j>√X, there are O(X^{3/4} log X) multiples up to X even without the hub restriction. For j=2 sum X/n² over n>X^{1/4}. For j≥3 sum X/n^j over n>X^{1/(2j)}, bounded by X(X^{-1/2}+X^{-1/2+1/(2j)}/(j−1)) for each j by the decreasing-function integral test. There are O(log X) exponents. This proves the displayed necessity. The estimate on Ψ is used only in this section. [Hildebrand and Tenenbaum, Theorem 1.1 and Dickman estimates](https://tenenb.perso.math.cnrs.fr/PPP/Survey_friables.pdf)

## Verification, credits and next obstruction

The asymptotic arguments are written proofs. The upper and lower powers agree in sections 1–3, and section 4 determines the order up to constant factors. Section 7 gives a necessary bound only. The accompanying program verifies a 42-modulus example by enumerating its full period and independently examining every base residue assignment after contraction. A separate Lean file checks the logical contraction across independent prime branches, including arbitrary row selection. The finite example uses the elementary CRT to pass to the product coordinates. See the verification record for the exact scope. No priority or full-solution claim is made. The quantity left uncontrolled in the unrestricted minimum is the number of exterior branches that can interact **within the same modulus** when the vertex-cover number is large. The optimizers constructed here give no justification for treating such moduli as independent.

[Erdős and Graham's problem](https://www.erdosproblems.com/latex/1189) · [Öztürk's reciprocal bounds](https://doi.org/10.13140/RG.2.2.16138.63684) · [Earlier every-size construction](../reciprocal-sums/erdos1189-reciprocal-sums-and-exact-minima.pdf) · [Earlier result about labels](../sparse-labels/sparse-labels.pdf) · [Prescribed-prime construction](../prime-budget/prime-budget.pdf)
