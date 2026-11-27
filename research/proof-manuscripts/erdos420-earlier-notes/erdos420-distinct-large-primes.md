# Two distinct large primes at one starting integer

Let \(P(m)\) be the largest prime factor of \(m\), and let \(d_i\) be the full part of \(n+i\) supported on primes at most \(h\), with multiplicity. Thus \(r_i=(n+i)/d_i\) has every prime factor greater than \(h\). A perfect power means \(u^t\) with integers \(u,t\ge 2\). All logarithms are natural.

**Theorem.** Fix \(A>1\), take \(h=\lfloor(\log n)^A\rfloor\), and write \(B=\tfrac32(1-1/A)\). At every sufficiently large starting integer, the proportion of offsets \(1\le i\le h\) for which \(d_i\le h^B\) and \(r_i\) is not a perfect power satisfies
\[
 \liminf_{n\to\infty}\frac1h\#\{i:d_i\le h^B,\ r_i\text{ is not a perfect power}\}
 \ \ge\ \max\{0,\tfrac13+\log(1-1/A)\}.
\]
The lower bound is positive for \(A>1/(1-e^{-1/3})\), in particular for every \(A\ge 4\). At \(A=4\) it exceeds 4.56 percent and the cofactor cutoff is \(h^{9/8}\).

Consequently any such interval **either contains** \(n+i=sp\) with \(s\le h^B\) and \(p\) prime, **or** the stated lower proportion of rows each has at least two distinct prime divisors greater than \(h\). For those rows \(d_i\le h^B\) and the full remaining factor is not a perfect power. Every prime greater than \(h\) occurs in at most one of the rows. The earlier smooth-part argument allowed the two large factors of a row to be powers of the same prime. The new conclusion excludes this possibility even when the exponents of the proposed powers vary arbitrarily between rows.

## Product coincidences at one start

Fix an integer \(k\ge2\). For sufficiently large \(n\), uniformly for integers \(2\le t\) and \(1\le j\le k\), two disjoint lists of \(j\) distinct offsets each from \([1,h]\) have products
\[
 F(n)=\prod_{i\in I}(n+i),\qquad G(n)=\prod_{i\in J}(n+i)
\]
whose ratio cannot be a rational \(t\)-th power. Here and below \(h\) is polylogarithmic in \(n\).

For \(t>j\), a rational-power ratio would give \(F(n)=d u^t,\ G(n)=d v^t\) for integers \(d,u,v\ge1\), by reducing the rational ratio first. If \(u\ne v\), the difference between the two values is at least the smaller value divided by its base (use \((b+1)^t-b^t\ge b^{t-1}\)). It is at least \(c_k n^{j-j/t}\), whereas both products lie between \(n^j\) and \((n+h)^j\) and differ by \(O_k(hn^{j-1})\). These inequalities contradict \(j/t\le k/(k+1)\). If \(u=v\), the polynomial \(F-G\) would vanish at \(n\). It is a nonzero integer polynomial of degree at most \(j-1\), with coefficients bounded by \(C_k h^k\). Its positive roots are bounded by \(1+C_k h^k\), using the usual root bound.

For \(2\le t\le j\le k\), put \(W(X)=F(X)G(X)^{t-1}\). Its leading term is \(X^{jt}\). Expand its positive real \(t\)-th root at infinity as
\[
 W(X)^{1/t}=Q(X)+O_k(h^{j+1}/X)\qquad(X\ge 2kh),
\]
where \(Q\) is the polynomial part, of degree \(j\). Indeed, expand the factors \((1+i/X)^{1/t}\) for \(i\in I\) and \((1+i/X)^{(t-1)/t}\) for \(i\in J\) through total degree \(j\), and multiply by \(X^j\). The discarded tail has the bound shown (Taylor's theorem on a fixed disk in \(h/X\) suffices). Each coefficient of \(X^{j-l}\) in \(Q\) is \(O_k(h^l)\), with denominator dividing a fixed \(D_k\) since \(t,j\le k\). If the ratio were a rational \(t\)-th power, \(W(n)\) would be an integer \(t\)-th power. The approximation is then within \(o(1/D_k)\) of its integer root at the rational \(Q(n)\), forcing equality. But \(W-Q^t\) is nonzero, since a root at \(-i\) for \(i\in I\) has multiplicity one in \(W\). After clearing bounded denominators its coefficients are \(O_k(h^{k^2})\), so its integer roots have magnitude \(O_k(1+h^{k^2})\). This excludes \(n\) for every fixed \(k\).

The role of the fixed \(k\) matters. Its constants may grow with \(k\). It will be chosen once below for each pair of fixed real exponents, before sending \(n\) to infinity.

## Smooth parts as edges of a graph

Write \(\eta=1/A\). Choose \(0<\gamma<1-\eta\), and put \(y=h^\gamma\). Remove every offset divisible by a prime \(p\in(y,h]\). By counting at most \(h/p+1\) multiples per prime, the removed proportion is at most \(-\log\gamma+o(1)\), by Mertens' prime reciprocal estimate. For each prime \(p\le y\), delete one more offset attaining the maximum \(p\)-valuation over the original full window. This costs at most \(\pi(y)=o(h)\) rows. On the surviving rows the sum of \(\log d_i\) is at most
\[
 \sum_{p\le y}v_p((h-1)!)\log p\le h\sum_{p\le y}\frac{\log p}{p-1}
 = h(\log y+O(1)).
\]
Indeed the deleted maximum removes at least one multiple of each prime power that appeared, leaving at most \(\lfloor(h-1)/p^a\rfloor\) multiples of \(p^a\). Markov's inequality for this nonnegative sum discards at most \((2/3+o(1))h\) additional rows to ensure \(d_i\le y^{3/2}\). There remain at least \((1/3+\log\gamma-o(1))h\) rows with this size bound and every prime factor of \(d_i\) at most \(y\).

Each such \(d_i\) factors as \(u_i v_i\) with positive integers \(u_i,v_i\le y\). When \(d_i\le y\) this is immediate. Otherwise, if any prime exceeds \(\sqrt y\) take it for \(u_i\). If none does, multiply prime factors in sequence until their product first reaches \(\sqrt y\). In both cases the selected factor lies in \([\sqrt y,y]\) and its complementary factor is at most \(y\).

For a fixed \(t\ge2\), draw an edge \((u_i,v_i)\) in a bipartite graph for each of the surviving rows whose \(r_i\) is a \(t\)-th power. Take two copies of \([1,\lfloor y\rfloor]\) for the vertex sets. A pair of parallel edges is impossible by the product lemma with \(j=1\). In a cycle of length \(2j\le2k\), the products of \(d_i\) on the two alternating groups of edges are identical, since each vertex is used once on either side. Hence the ratio of the corresponding products of \(n+i\) is a rational \(t\)-th power, again impossible. The graph has girth greater than \(2k\).

A simple graph on \(v\) vertices with girth greater than \(2k\) has \(O_k(v^{1+1/k})\) edges. To see this, prune vertices of degree below half the original average degree. A nonempty subgraph remains if there was an edge, by counting the edges lost on deletion. If the remaining minimum degree is \(m\ge2\), breadth-first nonbacktracking paths from a root to depth \(k\) have distinct endpoints at each depth, and give \(v\ge (m-1)^k\). Bounded average degree already gives the asserted estimate.

The total number of possible exponents is \(O(\log n/\log h)\), since each root of \(r_i>1\) is an integer with prime factors greater than \(h\). Fix \(k\) so that \(\gamma(1+1/k)+\eta<1\). The number of rows discarded over **all** exponent choices is therefore
\[
 O_k\!\bigl((\log n/\log h)y^{1+1/k}\bigr)=o(h).
\]
The remaining rows satisfy \(d_i\le y^{3/2}\le h^B\). First pass to the limit inferior in \(n\), then let \(\gamma\) increase to \(1-\eta\). This proves the result.

## Limit of the method

The graph detects common prime-power structure among many different offsets. Two *distinct* primes in a single rough part may have arbitrary relative sizes. No collision argument above controls the smaller of them, or supplies a prime larger than \(n/h^B\). The theorem is an unconditional obstruction for an individual interval in the exact arithmetic reduction. The uniform hit in Erdős #420(i) remains open. No priority claim or public submission has been made.

[Formal statement of #420](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/ErdosProblems/%C2%AB420%C2%BB/) · [Erdős, Graham, Ivić and Pomerance, *On the number of divisors of n!*](https://math.dartmouth.edu/~carlp/factorial.pdf) · [Subsequent work on long runs](https://arxiv.org/abs/2609.15597). The elementary polynomial-part argument is in the tradition of proofs excluding perfect powers among products of closely spaced integers. Its use here allows the power and its base to vary between different rows before grouping by exponent.

Related classical work is [Erdős and Turk, *Products of integers in short intervals* (1984), especially §§5–6](https://doi.org/10.4064/aa-44-2-147-174). They study equal products and perfect powers in short intervals. The product condition used in the graph here imposes balanced cardinalities on the two sides of a rational-power relation. That condition ensures integral degree in the polynomial-part argument.

The companion finite test compares all same-cardinality subsets of up to four terms from ten-term windows at twelve specified starts, including six constructed to have an exact large-prime-power row. It independently checks samples by integer roots of coprime numerators and denominators, and checks the elementary factorization of small smooth parts by enumerating possible factor pairs.
