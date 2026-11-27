# Pair probabilities in local bounds for progression-free sets

*Jordan Pollard, November 27, 2026*

Jordan Pollard directed the research. OpenAI Codex developed the proofs, computed the finite certificates, and drafted the manuscript.

How much does an upper bound for a progression-free set improve when two overlapping lists of positions must agree on the probability of selecting each pair? With only individual probabilities, ten positions are needed to push the limiting density below one half. With pair probabilities, five suffice. We compute the exact limiting densities through seven positions. For larger lists we give a limit on the method: for every fixed power of $\log N$, lists of that size still permit a density asymptotically larger than the maximum possible on $[N]$. [Earlier one-point calculation](https://github.com/jpollard-cs/open-math-agents/blob/3da3e43e28f38337cd492df7181130d36dc454bc/research/proof-manuscripts/erdos142-local-bounds/local-progression-bounds.pdf)

## 1. Which probabilities have to agree?

Write $r_3(N)$ for the maximum size of a subset of $[N]=\{1,\ldots,N\}$ containing no three distinct points in arithmetic progression. For every $i$ assign a number $x_i$ and for every distinct unordered pair $\{i,j\}$ a number $y_{ij}$, all in $[0,1]$. Call the assignment feasible at size $L$ if every $S\subseteq[N]$ of size at most $L$ admits a random progression-free subset $A_S$ with
$$
 \Pr(i\in A_S)=x_i,\qquad \Pr(i,j\in A_S)=y_{ij}\quad(i,j\in S,\ i\ne j).
$$
These conditions determine the full two-bit law of every pair. Different lists may choose different joint distributions on three or more indices. Let $V_L(N)$ be the maximum of $\sum_i x_i$ under these conditions. An actual progression-free set gives a feasible zero-one assignment, so $r_3(N)\le V_L(N)$.

**Theorem 1.** For fixed $L$, the limit $v_L=\lim_{N\to\infty} V_L(N)/N$ exists. Its first values and one choice of common pair marginal $q$ attaining each value are
$$
\begin{array}{c|ccccc}
 L & 1,2 & 3 & 4 & 5 & 6,7\\ \hline
 v_L & 1 & 2/3 & 1/2 & 4/9 & 3/7\\
 q & 1 & 1/3 & 1/6 & 1/6 & 1/7 .
\end{array}
$$
In particular $V_4(N)\ge N/2$ for every $N$, and $V_5(N)<N/2$ for all sufficiently large $N$.

**Reduction to two numbers.** Given $p,q\in[0,1]$, say they work on $S$ if a law as above exists with every single marginal equal to $p$ and every pair marginal equal to $q$. We claim $v_L$ equals the largest $p$ for which some $q$ works on every integer list of size at most $L$. Such a pair immediately gives $V_L(N)\ge pN$ for all $N$.

For the reverse bound choose optimal arrays on intervals tending to infinity along the limsup. Extend each array by zero on singles outside the interval and on pairs with an endpoint outside. Every list in $\mathbb Z$ remains feasible by using its intersection with the interval. Average the shifted arrays with shifts $1,\ldots,N$. The average at site zero is $V_L(N)/N$. Translating this average by any fixed $h$ changes each entry by at most $2|h|/N$. By a diagonal subsequence the averaged arrays converge at every site and pair. Feasibility on each finite list is closed and convex, being a projection of a finite probability simplex. The limiting feasible array therefore has constant single marginal $p=\limsup V_L(N)/N$ and a pair marginal $\beta_d$ depending only on the positive distance $d$.

Dilating indices by a positive integer $m$ preserves feasibility, since it preserves the progressions of each list. Let $\ell_1,\ell_2,\ldots$ be the primes and average the dilated arrays over
$$
 F_t=\left\{\prod_{j=1}^t\ell_j^{e_j}:0\le e_j<t\right\}.
$$
For each fixed $d$ and sufficiently large $t$, the proportion $|F_t\mathbin{\triangle}dF_t|/|F_t|$ is at most $2\Omega(d)/t$, where $\Omega$ counts prime factors with multiplicity. This follows by shifting the exponent box in its prime coordinates. Pass to a subsequence on which the mean of $\beta_m$ over $F_t$ converges to $q$. The mean of $\beta_{md}$ then tends to the same $q$ at every fixed distance $d$. The limiting array is feasible on every finite list of size at most $L$. This proves the claim. In testing a common pair it suffices to check size exactly $L$, because any smaller list can be extended and the resulting distribution restricted.

## 2. Exact finite certificates

**Upper bounds.** A three-term progression gives $3p\le2$. For four positions use $\{0,1,2,4\}$, with $Z_a$ denoting membership at the integer $a$. Every admissible subset satisfies
$$
 Z_1+Z_4-Z_1Z_4+Z_0Z_2\le1.
$$
Indeed $Z_0Z_2=1$ excludes both 1 and 4. On taking expectations the pair terms cancel, leaving $2p\le1$.

For the five- and six-position bounds, index each list by $0,\ldots,n-1$ in increasing order. The certificate is an inequality $c+\sum_i a_i Z_i+\sum_{i<j}b_{ij}Z_i Z_j\le0$, with $b$ listed in lexicographic order of the pairs.

1. On $(0,1,2,3,4)$ take $c=0$, $a=(0,-1,-1,-1,0)$ and $b=(1,1,-1,0,2,2,-1,2,1,1)$. This gives $-3p+8q\le0$.
2. On $(0,2,3,4,6)$ take $c=-1$, $a=(1,0,1,0,1)$ and $b=(0,-1,0,-1,0,1,0,0,-1,0)$. This gives $3p-2q\le1$.
3. On $(0,1,2,3,4,5)$ take $c=-12$, $a=(5,7,2,2,7,5)$ and
   $b=(0,5,-5,0,-5,3,3,-10,0,3,3,-5,3,5,0)$. This gives $28p\le12$.

Direct substitution over the at most $2^n$ bit strings checks each pointwise inequality after discarding strings containing a progression. Multiplying the second expected inequality by four and adding the first gives $9p\le4$. The six-site bound also applies at seven sites.

**Lower bounds.** Through two sites take the whole list. At three or four sites choose a uniformly random pair. This gives the stated single and pair marginals and never produces a triple.

For five sites, every realizable set of forbidden triples is contained, after relabeling, in one of the two five-site patterns above. Here are distributions for those two patterns. Encode a subset by the sum of $2^i$ over its indices $i$. Each entry $(w;M)$ assigns weight $w/54$ to **each** subset code in $M$.
$$
\begin{aligned}
(0,1,2,3,4):\quad &(3;\{0\}),\ (6;\{3,10,17,24\}),\ (3;\{5,6,12,20\}),\\
 &(6;\{13,22\}),\ (3;\{27\}).\\[2pt]
(0,2,3,4,6):\quad &(4;\{1,4,16\}),\ (1;\{3,6,9,12,18,24\}),\\
 &(1;\{5,17,20\}),\ (4;\{7,13,19,22,25,28\}),\ (9;\{10\}).
\end{aligned}
$$
In each law the numerators sum to 54, every point has total weight 24 and every pair has weight 9. All positive-weight subsets avoid the listed progressions. A law for a pattern also works when some of its forbidden triples are removed.

For seven sites use the seven lines of a Fano plane. On the labels $1,\ldots,7$ take the triples whose binary exclusive-or is zero. Every pair belongs to one line and every point belongs to three. For every seven-site integer list there is a permutation assigning these labels so that **none of the seven lines is an arithmetic progression**. Choosing a uniformly random line then gives $(p,q)=(3/7,1/7)$. Restricting a law from seven sites also gives the six-site lower bound.

**How to verify coverage.** Write positive gaps $g_i$ between adjacent points. A true progression imposes equality of two consecutive sums of gaps. Impose all midpoint equations of a given pattern, normalize gaps by $g_i\ge1$, and minimize their sum. A minimizing vertex exists since the nonempty objective sublevels are bounded. At a vertex there are $n-1$ independent active equations, at least one a unit-gap equation. The accompanying enumerator tries all such bases, discards invalid solutions, clears denominators, and computes every progression in the resulting integer list. Every original pattern is contained in one so obtained. Retaining only inclusion-maximal masks yields respectively $1,3,16,152,2238$ ordered patterns for $n=3,\ldots,7$.

Run the companion program `python check_pairs.py` with standard Python 3 and a C++17 compiler. It builds the companion `templates.cpp`, checks the upper inequalities on every admissible subset, verifies the five-site moment sums and containment under relabeling, and tries all 30 labeled Fano planes against each of the 2,238 seven-site patterns. All certificate checks use integer arithmetic.

## 3. An obstruction for growing lists

**Theorem 2.** There is an absolute $C>0$ such that, for every $L\ge3$, every list of at most $L$ integers admits a random progression-free subset with pairwise independent membership indicators, each of mean $\rho_L=\exp(-C\sqrt{\log L})$. The same $\rho_L$ works for all lists, irrespective of their diameters.

**A small prime model.** For $2\le s\le L$ ordered integers set the first coordinate to zero. In the remaining $s-1$ coordinates impose every midpoint equation of the list and require all adjacent gaps to be at least one. Minimize the last coordinate. As above take a vertex with $s-1$ independent active equations. Each matrix row has squared Euclidean norm at most 6 and right-hand side zero or one. Replacing any column by the right-hand side gives row norms at most $\sqrt7$. By Cramer's rule and Hadamard's determinant bound, after multiplication by the absolute determinant the vertex has integer coordinates
$$
 0=z_1<z_2<\cdots<z_s\le 7^{(s-1)/2}.
$$
These coordinates preserve every original progression. Let $D=\prod_{i<j}(z_j-z_i)$. Then $\log D\le\binom{s}{2}(s-1)(\log 7)/2$. By the prime number theorem, for a large enough absolute $C_0$ the sum of the logarithms of primes in $[L^3,C_0 L^3]$ exceeds this bound. Enlarging $C_0$ handles finitely many small $L$. Some prime $P$ in this interval does not divide $D$. Reduction modulo $P$ gives an injection of the sites into $\mathbb F_P$ that preserves all their midpoint equations. Additional progressions in its image are harmless.

**A pairwise independent law.** Put $M=\lfloor L^3/2\rfloor$ and let $B$ be a largest progression-free subset of $\{0,\ldots,M-1\}$, of size $b=r_3(M)$. It remains progression-free modulo $P$, since the absolute value of a nonzero midpoint discrepancy is at most $2(M-1)<P$. Apply a uniformly random invertible affine map of $\mathbb F_P$ to $B$. The affine group is doubly transitive, so a specified site has inclusion probability $b/P$ and a specified pair has joint inclusion probability $b(b-1)/(P(P-1))$.

Independently keep this entire sample with probability $\theta=P(b-1)/(b(P-1))$, returning the empty set otherwise. The new single-site probability and the new pair probability are exactly
$$
 r=\frac{b-1}{P-1},\qquad r^2=\frac{(b-1)^2}{(P-1)^2}.
$$
Pull back to the list by the injection above. Each chosen subset is progression-free because its image is. Behrend's lower bound $b\ge M\exp(-C_1\sqrt{\log M})$ for large $M$, together with $P\le C_0L^3$, gives $r\ge\rho_L$ after fixing a sufficiently large $C$. Independently keeping each selected site with probability $\rho_L/r$ equalizes the density across lists and preserves pairwise independence. A singleton has the required Bernoulli law as well. [Behrend (1946)](https://doi.org/10.1073/pnas.32.12.331)

**Comparison with the integer problem.** The common array $x_i=\rho_L$, $y_{ij}=\rho_L^2$ gives $V_L(N)\ge N\rho_L$. It even obeys global positive semidefiniteness of the matrix of first and second moments of $(1,Z_1,\ldots,Z_N)$, since the Schur complement of the top-left entry is $\rho_L(1-\rho_L)I$. This extra constraint can change the exact small-list optima in Theorem 1.

Raghavan's upper bound for actual progression-free sets is $r_3(N)/N\le \exp(-c(\log N)^{1/6}/\log\log N)$ for sufficiently large $N$. Comparing the two exponents gives
$$
 \frac{V_L(N)}{r_3(N)}\longrightarrow\infty
 \quad\text{if}\quad
 3\le L\le N,\qquad
 \log L=o\!\left(\frac{(\log N)^{1/3}}{(\log\log N)^2}\right).
$$
The same divergence holds with the global positive semidefinite constraint, and includes every fixed power of $\log N$. Determining the unrestricted order of $r_3(N)$ is still open. Theorems 1 and 2 concern the power of these particular local bounds. Their proofs and finite certificates are provided for independent review. [Raghavan (2026)](https://arxiv.org/abs/2603.27045), [Erdős problem 142](https://www.erdosproblems.com/142)
