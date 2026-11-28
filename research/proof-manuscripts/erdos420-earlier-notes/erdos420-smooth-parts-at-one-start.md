# Erdős #420(i): what a sieve of the small prime factors leaves at one start

The question is whether some fixed polylogarithmic window gives unbounded growth of \(\tau(n!)\) at every sufficiently large \(n\). The earlier reduction asks whether every such \(n\) admits an integer \(n+i=sp\) with \(i,s\le\lfloor(\log n)^A\rfloor\) and \(p\) prime, for some fixed \(A\). This checkpoint studies the factors present in a proposed individual counterexample. The uniform prime hit remains open.

## A binomial coefficient at the exact cutoff

For positive integers \(n,h,H\) with \(n\ge hH\), there is an \(n+i=sp\) with \(1\le i\le h,\ 1\le s\le H\) and \(p\) prime if and only if
\[
P\!\binom{n+h}{h}>\frac nH,
\]
where \(P\) is the largest prime divisor. A hit gives \(p=(n+i)/s>n/H\ge h\), hence \(p\) divides the product of the \(h\) numerator factors and survives division by \(h!\). Conversely such a prime divides some \(n+i\). It satisfies \((H+1)p>n+h\) since \(Hp>n\) and \(p>h\). The integral cofactor is therefore at most \(H\). A separate direct-factorization check agreed in 20,705 integer triples.

In Erdős #961, \(f(k)\) is the least number of consecutive integers above \(k\) that always contain a multiple of a prime greater than \(k\). The identity locates #420(i) inside that extremal question at \(k=\lfloor n/H\rfloor\) and polylogarithmic \(H\). A bound \(f(k)\ll(\log k)^b\) over all starts would imply the desired hit by taking \(h=H=\lfloor(\log n)^A\rfloor\) with \(A>b\). Such a global estimate would also give polylogarithmic prime gaps by considering starts near \(k\). The cited work does not prove this global estimate. [Erdős #961](https://www.erdosproblems.com/961) · [Bauer and Bennett](https://personal.math.ubc.ca/~bennett/erdos-graham3.pdf)

## Many bounded smooth parts, uniformly in the starting integer

Let \(h\ge2\), and write the full \(h\)-smooth part and its complementary factor as
\[
d_i=\prod_{p\le h}p^{v_p(n+i)},\qquad r_i=(n+i)/d_i .
\]
For each prime \(p\le h\), choose an index \(a_p\) maximizing \(v_p(n+a_p)\). Delete the set of these at most \(\pi(h)\) indices. Then
\[
\prod_{i\notin\{a_p:p\le h\}}d_i\ \mid\ (h-1)! .
\]
Indeed, for a given prime power \(p^j\), let \(t\) of the original indices give a multiple. If \(t>0\) its chosen maximizing position is one of them. The remaining count is at most \(t-1\le\lfloor(h-1)/p^j\rfloor\), by the spacing of multiples. Sum over \(j\) and apply Legendre's formula. This is the classical maximal-valuation deletion argument in Erdős's treatment of the Sylvester–Schur theorem. [Erdős, *Problems and results on consecutive integers* (1976), especially Theorem 1 and its proof](https://publi.math.unideb.hu/paper/3385/download/10_5486_PMD_1976_23_3-4_15.pdf)

Fix \(a>1,\ b>0\). At every start \(n\), at least
\[
h-\pi(h)-\frac{\log((h-1)!)}{a\log h}
\]
offsets satisfy \(d_i\le h^a\), a proportion at least \(1-1/a-o(1)\). For these offsets, failure of **every** hit with cofactor at most \(h^{a+b}\) implies
\[
r_i/P(r_i)> h^b .
\]
Here assume \(n>h^{a+3b}\). In particular \(r_i>h^{3b}>1\), and every prime of \(r_i\) is greater than \(h\). Indeed otherwise \(d_i r_i/P(r_i)\le h^{a+b}\) would give an actual qualifying cofactor.

Each such \(r_i\) can be split as \(u_i v_i\) with **both** \(u_i,v_i>h^b\). If \(P(r_i)>h^b\), take \(u_i=P(r_i)\). In the other case, multiply prime factors with multiplicity until their product first exceeds \(h^b\). The resulting product is at most \(h^{2b}\), so its complementary factor exceeds \(h^b\). Between different offsets the resulting products \(u_i v_i\) are pairwise coprime, since a shared prime would exceed \(h\) and divide an offset difference smaller than \(h\). The two factors at the same offset can have a common prime. All displayed comparisons to real powers have the same meaning for integer cofactors as comparisons to their floors.

Consequently, a uniform counterexample interval must sustain this pattern of composite remainders across a positive proportion of its actual offsets. The pattern by itself can also occur in successful intervals. In particular a composite \(r_i\) may have a prime divisor with cofactor within budget. This is where the smooth-part sieve stops.

## An exact finite calculation for the smooth-part screening step

For fixed integer cutoffs \(h\ge2,\ U\ge1\), the minimum over all starting integers of \(\#\{i:d_i\le U\}\) equals the following finite minimum. For every prime \(p\le h\), choose an offset \(a_p\in\{1,\dots,h\}\). Count the indices \(i\) outside the chosen offsets for which
\[
\prod_{p\le h}p^{v_p(|i-a_p|)}\le U,
\]
and minimize that count over all choices. For any actual interval, take its maximizing indices as above. Off these indices, \(v_p(n+i)\le v_p(i-a_p)\), since \(p^{v_p(n+i)}\) divides both \(n+i\) and \(n+a_p\). Thus the model count is no larger than the actual count. Conversely fix any choices and take \(p^{e_p}>\max(h,U)\) for every \(p\le h\). The Chinese remainder theorem permits \(n\equiv-a_p\bmod p^{e_p}\) simultaneously. The indicated valuations off the chosen indices then agree exactly, and every chosen index has smooth part exceeding \(U\). This realizes the minimum for arbitrarily large representatives with fixed \(h,U\).

For \(U=h\), the minima for \(h=2,\dots,10\) are respectively \(1,1,1,1,2,1,2,2,3\). Two independent exhaustive calculations agreed. One enumerated the minimizing offset choices. The other scanned all starts modulo the product of the least prime powers \(p^{e_p}>h\), counting the \(h\) values with gcd at most \(h\). This is an exact finite result about smooth parts. It does not compute how often the remaining factor is prime.

## What remains

The product bound certifies many offsets with a small \(d_i\), whereas part (i) requires finding a sufficiently large prime at one of them or at another offset. The binomial formulation requires \(P(\binom{n+h}{h})>n/H\). A prime greater merely than the window length \(h\) falls far short when \(h,H\) are polylogarithmic. No published priority is claimed for these elementary consequences. No submission was made.
