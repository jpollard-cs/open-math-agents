# Distinct multiples of all primes in a random interval

## The question and the answer

Start at an integer $m$ and choose a different multiple of each prime up to $n$, all after $m$. Erdős and Pomerance asked how far one must go on average. They averaged over one full primorial period and asked whether the average divided by $n$ can be unbounded. This is the question on printed page 159, immediately before their definition of the worst-case length. [Original paper, §6](https://math.dartmouth.edu/~carlp/PDF/matching.pdf#page=13)

Let $P_n=\prod_{p\le n}p$, with the product over primes. Choose $m$ uniformly in $\{0,\ldots,P_n-1\}$. Let $F_n(m)$ be the least integer $h$ for which one can choose distinct integers $m+x_p$, one for each prime $p\le n$, satisfying
$$
1\le x_p\le h,\qquad p\mid m+x_p .
$$
This gives the half-open interval in the original paper. Changing the right endpoint to a strict inequality adds one to the minimum when $n\ge2$.

**Theorem.** With natural logarithms and $a_n=(n\log n)^{2/3}$, for each fixed $t\ge0$,
$$
\lim_{n\to\infty}\Pr\{F_n\le\lfloor 2n-t a_n\rfloor\}
=\exp(-t^3/24).
$$
In particular $(2n-F_n)/a_n$ converges in distribution to a nonnegative Weibull variable with this survival function. The actual average has the two-term expansion
$$
\frac1{P_n}\sum_{m=0}^{P_n-1} F_n(m)
=2n-24^{1/3}\Gamma(4/3)(n\log n)^{2/3}
+o\big((n\log n)^{2/3}\big).
$$
The correction coefficient is approximately $2.57580$. For every fixed $2\le c<3$ the fraction of starts requiring more than $cn$ is $n^{-1+o(1)}$.

This is a proposed proof of the average over the full primorial period in Erdős and Pomerance, §6, p. 159. The associated problems about the maximum over starting positions have different quantifiers. [Erdős #711](https://www.erdosproblems.com/711) · [Erdős #860](https://www.erdosproblems.com/860)

## 1. Independent choices and rows with a single option

Let $R_p\in\{1,\ldots,p\}$ be the first offset divisible by $p$ after adding $m$. The Chinese remainder theorem makes the $R_p$ independent and exactly uniform. The available offsets for row $p$ form $R_p,R_p+p,\ldots$, cut off at $h$.

Write $h=2n-s$, with $s$ an integer and $n\le h\le2n$. Row $p$ has a single option precisely when $R_p\in I_p=(h-p,p]\cap\mathbb Z$. The possible such primes form $B=\{p:h/2<p\le n\}$. The intervals $I_p$ are nested and have size $2p-h$. Let $Z$ count unordered pairs of distinct primes with the same single option. Such a pair prevents any matching. Independence gives the exact mean
$$
\lambda_n=\mathbb EZ
=\sum_{h/2<q<p\le n}\frac{2q-h}{pq}.
$$

For $s\sim t a_n$ with fixed $t>0$, the prime number theorem in short intervals applies on every fixed positive fraction of $s$, since $2/3>7/12$. Thus $K=|B|\sim s/(2\log n)$, and the measure assigning mass $\log n/s$ to each $(n-p)/s$ for $p\in B$ converges weakly to Lebesgue measure on $[0,1/2]$. To see this, apply the short-interval theorem on each fixed subinterval with positive length. In the pair sum the factors $pq/n^2$ tend to one uniformly and the diagonal has negligible mass. Consequently
$$
\lambda_n\sim\frac{s^3}{n^2\log^2 n}
\int_0^{1/2}v(1-2v)\,dv
=\frac{s^3}{24n^2\log^2 n}\ \longrightarrow\ t^3/24.
$$
[Vaughan, Theorem 28.5 on primes in short intervals](https://personal.science.psu.edu/rcv4/597-5f25/Class597-28.pdf)

The pair count converges to a Poisson variable of this mean. For a fixed ordered list of distinct pairs, consider the graph of its prime labels. Within a connected component on $v$ labels every first offset must equal the same single option. There are at most $s$ common values and every $p\in B$ is comparable to $n$. Summing over label choices bounds the contribution of a component by $O_v(s(K/n)^v)$. This is bounded for $v=2$ and tends to zero for every fixed $v\ge3$. Disjoint components are independent. There are finitely many graph types at each fixed moment order. Therefore only disjoint pairs contribute in the limit. Their sum of products is $\lambda_n^k+o(1)$ at order $k$. Indeed the expansion of $\lambda_n^k$ on nondisjoint labels is $O_k(K^{2k-1}(s/n^2)^k)=o(1)$. This proves the Poisson claim by factorial moments. In particular $\Pr(Z=0)\to e^{-t^3/24}$.

## 2. Small primes can use the slots left over

We prove that, with probability tending to one, these direct collisions are the only obstructions at this scale. Let $y=n/(\log n)^2$. For each $p>y$ keep its first two offsets, when present, and at most these two. Let $D$ be the union of the retained offsets. The following estimates apply uniformly for $n\le h\le2n$.

For a fixed prime $q\le y$, condition on $R_q$. Its row has $M_q\ge\lfloor h/q\rfloor$ positions. A fixed $p>y$ can consume at most one such position since $q\nmid p$. Its probability of doing so is at most $2(1/q+1/p)\le4/q$ by counting possible first offsets in either of the two residue classes modulo $q$. Conditional on $R_q$, these indicators are independent over $p>y$. Their sum has mean $O(n/(q\log n))$. By the elementary upper tail bound $\Pr(X\ge k)\le(e\mathbb EX/k)^k$ for a sum of independent Bernoulli variables, losing at least $M_q/2$ positions has probability $O_A(n^{-A})$ for every fixed $A>0$, uniformly in $q$. Here $M_q\gg(\log n)^2$. The same conclusion holds simultaneously over all small primes by a union bound.

For any fixed column $x\le h$, the number of small-prime rows containing it is a sum of independent Bernoulli variables of mean $\sum_{q\le y}1/q=O(\log\log n)$. The same inequality, followed by a union bound over $x$, shows that all column degrees are at most $\lceil\log n\rceil$, outside an event of probability $O_A(n^{-A})$. Every small row outside $D$ now has degree greater than this maximum column degree. Counting incident edges for any set of rows proves Hall's condition. The small rows can therefore be matched using only columns outside $D$, independently of how the retained columns are eventually assigned to the large rows.

## 3. The graph of large primes

Each large row with two retained offsets gives an undirected edge of length $p$. A row with one gives a mark at its unique vertex. In a tree bearing at most one mark, root the tree at the marked vertex, or at any vertex if there is no mark. Assign each edge to its child and each mark to its own vertex. Thus a forest admits the large-row matching whenever no tree contains two marks.

Write $S=2\sum_{y<p\le n}1/p=O(\log\log n/\log n)$. The bound follows, for example, by subdividing into dyadic intervals and using $\pi(x)\ll x/\log x$. To count possible paths, an initial vertex and a sequence of signed lengths determine the successive vertices. A specified edge of length $p$ is present with probability at most $1/p$, because its lower endpoint specifies $R_p$. Distinct labels are independent. In upper bounds one can drop distinctness *after* multiplying the probabilities for valid lists.

All large primes are odd, so the graph is bipartite. There are no parallel edges since distinct labels have distinct lengths. A simple cycle has length $k\ge4$. For each of at most $2n$ starting vertices expose the first $k-1$ signed lengths. The final edge length is then forced by the return to the starting vertex. Its probability is at most $1/y$ if it is an unused allowable prime. Summing over all lengths bounds the expected number of simple cycles by
$$
\frac{2n}{y}\sum_{k\ge4} S^{k-1}=o(1).
$$

Two different marks can occupy different vertices of the same tree only if a simple path of positive length joins them. For an ordered pair $p,q\in B$, the first mark has at most $s$ possible offsets, each with probability $1/p$. Expose $k\ge1$ signed lengths of other labels. The last vertex then forces the exact value of $R_q$, of probability at most $1/q$. Hence the expected number of such marked paths is at most
$$
s\Big(\sum_{p\in B}1/p\Big)^2\sum_{k\ge1}S^k
=O\!\left(\frac{s^3}{n^2\log^2 n}\right)o(1)=o(1)
$$
at the stated scale. For $Z=0$ no two marks already occupy the same vertex. The small-prime argument and the forest construction now give
$$
0\le \Pr(Z=0)-\Pr(F_n\le h)=o(1).
$$
At $t=0$ there are no marks and the same proof gives probability tending to one. This proves the distributional theorem including its endpoint.

## 4. Why the rare long intervals do not change the average

A sharper upper tail at $h=2n$ is needed to identify the second term of the mean. There are no marks at this length. A connected graph with at most one cycle can assign different vertices to all its edges. For a unicyclic component orient the cycle cyclically, orient all attached trees away from the cycle, and assign each edge to its head. Failure for large rows therefore requires a component containing a spanning tree and at least two extra edges.

For a tree on $v$ vertices there are at most $4^{v-1}$ rooted plane tree shapes, by its depth-first sequence of upward and downward steps. Enumerate a root column and all $v-1$ signed edge lengths in tree order. There are at most $v^4$ ways to specify endpoints of the two extra edges. Their lengths are forced. Keep only valid embeddings with distinct prime labels for every edge. Independence bounds the two extra probabilities by $y^{-2}$. Summing the tree weights costs at most $S^{v-1}$. Every component with at least two extra edges has such a witness. Hence
$$
\Pr(F_n>2n)\ll_A n^{-A}
+\frac{2n}{y^2}\sum_{v\ge1}v^4(4S)^{v-1}
=O((\log n)^4/n).
$$
Erdős and Pomerance's uniform $O(n^{3/2})$ bound for all integer rows also bounds our prime-row minimum. Multiplying by the displayed probability gives
$$
\mathbb E(F_n-2n)_+=O(n^{1/2}(\log n)^4)=o(a_n).
$$
[Original paper, Theorem 4](https://math.dartmouth.edu/~carlp/PDF/matching.pdf)

For the opposite tail take $a_n\le s\le n/2$. There are $\gg s/\log n$ primes in $(n-s/8,n]$ by the uniform short-interval prime number theorem. For every such prime $I_p$ contains the same set $J=(n-3s/4,n-s/4]\cap\mathbb Z$ of size comparable to $s$. The number $U$ with $R_p\in J$ is a sum of independent indicators with mean $\mu\gg s^2/(n\log n)$. The elementary Chernoff bound gives $\Pr(U<\mu/2)\le e^{-\mu/8}$. Given the identities of the primes that hit $J$, their locations are independent and uniform in $J$. A matching requires distinct locations. Conditional on $U\ge\mu/2$, the birthday bound gives probability at most $\exp[-c\mu^2/s]$ for an absolute $c>0$. This proves, uniformly in the indicated range,
$$
\Pr(F_n\le 2n-s)\ll \exp[-c' (s/a_n)^3].
$$
For $s>n/2$ use monotonicity and the value at $n/2$. The remaining integration range for the positive deficit has length at most $2n/a_n$ in normalized units. Its integral tends to zero. Integrating the distributional limit and using these bounds gives
$$
\frac{\mathbb E(2n-F_n)_+}{a_n}\longrightarrow
\int_0^\infty e^{-t^3/24}\,dt
=24^{1/3}\Gamma(4/3).
$$
Together the two tails prove the mean expansion.

## 5. Independent route to the leading constant

The conclusion $\mathbb E F_n/n\to2$ also has a shorter proof using the ordinary prime number theorem. Fix $0<\delta<1$. For primes in $(\delta n,n]$, keep the first two offsets in a length $2n$ interval. The cycle count in §3, with $y=\delta n$, gives $o_\delta(1)$ expected cycles. Delete one edge per independent cycle to obtain a forest. For each deleted edge allocate a fresh interval of length $n$ after the first $2n$ positions. Its prime has a multiple in that interval. This uses at most $2n+nC$ positions, where $C$ is the number of simple cycles. The length of this construction depends only on the large-prime residues. Conditional on them, the start of the next interval is still uniform modulo the small primorial, by the Chinese remainder theorem. Thus $G(n)=\mathbb E F_n$ obeys
$$
G(n)\le2n+o_\delta(n)+G(\lfloor\delta n\rfloor).
$$
First set $\delta=1/2$ and iterate to get $G(n)=O(n)$. Then take the limsup and send $\delta\downarrow0$ to get an upper constant of 2. For the lower constant, take $s=\varepsilon n$ for fixed $0<\varepsilon<1/2$ in the common-interval birthday argument in §4. The ordinary prime number theorem suffices and the probability of a matching tends to zero. This proves the leading constant without using the distributional calculation or the prime number theorem in short intervals.

## 6. How often can a start need between two and three times $n$?

For every fixed $2\le c<3$, the previous upper bound can be paired with an explicit family of obstructions. For sufficiently large $n$,
$$
\frac{c_1(c)}{n(\log n)^6}\ \le\ \Pr\{F_n>\lfloor cn\rfloor\}
\ \le\ \frac{C(\log n)^4}{n}.
$$
In particular the probability is $n^{-1+o(1)}$. The constants can depend on the fixed threshold in the lower bound. This counts actual bad starts over the full primorial period.

Put $\varepsilon=3-c$, $b=1-\varepsilon/2$, $d=1-\varepsilon/10$ and $\eta=\varepsilon/40$. Take the integer points of $I=[bn,(b+\eta)n]$ and $J=[(b+d)n,(b+d+\eta)n]$. Join $u\in I$ to $w\in J$ whenever $p=w-u$ is prime. Every such length satisfies $p\le n$, $1\le u\le p$, $w\le 2n$ and $u+2p>cn$ for all sufficiently large $n$. Thus forcing $R_p=u$ gives the row exactly the two possible offsets $u,w$ at horizon $\lfloor cn\rfloor$.

The graph has $\gg_c n^2/\log n$ edges. Indeed each prime within $\eta n/2$ of $dn$ occurs as the difference of $\gg_c n$ pairs, and the ordinary prime number theorem counts $\gg_c n/\log n$ such primes. There are $\gg_c n^5/(\log n)^6$ copies of the complete bipartite graph with two left and three right vertices. To verify the count, sum the number of common neighbors over left pairs. This sum equals $\sum_{w\in J}\binom{\deg(w)}2\gg_c n^3/(\log n)^2$ by convexity. Taking the sum of the third binomial coefficient of these common-neighbor counts, again by convexity, gives the asserted five-vertex count. At most $O(n^4)$ ordered five-tuples have two equal edge lengths. Such equality between different edges with distinct ends gives a nontrivial linear equation on the five coordinates, and equal lengths on edges with a common end are impossible. The same lower bound thus holds for copies with all six prime lengths distinct.

Call each such copy a witness, counting unordered vertex sets on both sides. It occurs if the six prescribed first offsets are realized. Its probability is the product of six reciprocal primes, of order $n^{-6}$. These six rows have only five available sites. Let $W$ count occurring witnesses. We have $\mathbb EW\gg_c 1/(n(\log n)^6)$.

To pass from expectation to probability, condition on one specified witness occurring. A second compatible witness sharing a label must share the entire edge of that label, since its first offset and length already determine its endpoints. If it shares $j$ vertices and $e$ edges, its remaining realization probability is $O_c(n^{-(6-e)})$. There are $O(n^{5-j})$ choices of its other coordinates. Every proper subgraph of the complete bipartite graph with sides two and three has at most as many edges as vertices. For at most four vertices this follows by checking the two side sizes, and on five vertices a proper subgraph has at most five edges. Hence $e\le j$ for a distinct witness, including a disjoint one. The conditional expected number of other witnesses is $O_c(1/n)$. Summing over first witnesses and applying the first two inclusion–exclusion terms gives $\Pr(W>0)\ge(1-O_c(1/n))\mathbb EW$. The upper estimate follows from §4 by monotonicity.

**An exact example.** For $n=79$ and $m=15{,}027{,}890{,}785$, the six primes $59,61,67,71,73,79$ have only the five offsets $29,41,100,102,108$ in the next 158 positions. Each of the six rows has two choices. At length 159 the new offset 159 serves row 59. In increasing prime order through 79 the following offsets certify a full matching.
$$
(1,2,5,9,16,15,7,14,3,43,47,22,17,34,88,45,159,41,108,100,102,29).
$$
Consequently $F_{79}(15{,}027{,}890{,}785)=159$. This example has an obstruction with no colliding singleton rows.

## References

1. P. Erdős and C. Pomerance, *Matching the natural numbers up to n with distinct multiples in another interval* (1980). Theorem 4 gives the uniform bound used in §4. Section 6, printed p. 159, asks for the prime-row average. [Original paper](https://math.dartmouth.edu/~carlp/PDF/matching.pdf)
2. R. C. Vaughan, *Zero Density Estimates*, Theorem 28.5, on the prime number theorem in short intervals. [Lecture notes](https://personal.science.psu.edu/rcv4/597-5f25/Class597-28.pdf)
