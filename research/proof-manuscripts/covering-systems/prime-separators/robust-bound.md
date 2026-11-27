# Disjoint pairs of large primes are forced in the moduli carrying the reciprocal sum

Codex (OpenAI). Unrestricted consequence for Erdős #1189(iii).

Let A be any irreducible set of k distinct covering moduli, with S(A)≥(c−o(1))log k. Suppose 0<δ<1/2 and
$$
 E(\delta)=e^\gamma\delta[1+\log(1/(2\delta))]<c.
$$
For all sufficiently large k, there are more than k^δ **different moduli at most k** in A to which one can assign pairs of distinct prime divisors, both exceeding k^δ, with no prime occurring in two chosen pairs. This still holds after deleting any family of moduli of total reciprocal mass o(log k). Thus one exceptionally large modulus containing many prime factors cannot by itself explain the vertex-cover bound.

Indeed first delete the permitted family and the rows above k, the latter costing at most one in reciprocal sum. Seek a matching greedily, insisting on distinct row representatives and avoiding every prime through k^δ. If at most k^δ pairs have been chosen, remove their representative rows and mark their primes. The representatives exceed k^{2δ}, so their total mass is ≤k^{-δ}. If no further pair exists, the primes through k^δ and the marked endpoints hit all but at most one prime of each remaining modulus. Their number is at most 3k^δ. The analytic upper estimate in section 6 of the [manuscript](prime-separators.md) applies to every subset of the original rows: the bound on the sum of p−1 over active primes is inherited, even though the subset need not cover. It bounds the retained mass by (E(δ)+o(1))log k, a contradiction.

In fact for *every* proposed set of at most 3k^δ shared primes, the rows ≤k having at least two prime factors outside it have total weight at least (c−E(δ)−o(1))log k. This follows by applying the same upper bound to the complementary subfamily, then discarding rows above k at cost at most one.

At the already attained value c=1/2 one may take δ=0.11 (the root of E(δ)=1/2 is approximately 0.112780841). This statement quantifies over every sufficiently large k in the family. It leaves open whether the unrestricted sum can exceed (1/2+ε)log k.

## Sharpening the cap on small moduli

One may replace E(δ) above by the following smaller coefficient:
$$
 C(\delta)=\delta\left[A(1/\delta)+
 \int_\delta^{1/2}A((1-v)/\delta)\,\frac{dv}{v}\right],
 \qquad A(u)=\int_0^u\rho(t)\,dt,
$$
where ρ is Dickman’s function. We include the proof to specify the improvement without relying on numerical quadrature.

With Y=√(k log k), rows ≤k involving an active prime p>Y have mass at most (1+log k)Σ_{p|lcm(A),p>Y}1/p=O(1) by Znám–Simpson. Drop them. For an upper bound allow every integer ≤k with all prime factors at most Y and at most one distinct factor outside the chosen hubs. Among hub sets of a fixed size this sum of reciprocals is maximized by the first primes. To exchange a smaller exterior prime p and a larger hub q, fix the factor n' coprime to pq. If n' has no outside prime the allowed p,q-parts are unchanged. If n' has two outside primes there are no choices. If it has one, the allowed extra parts are powers of the hub, including 1. Replacing each q^a by p^a for a≥1 preserves the upper cutoff and increases the reciprocal term. Enlarging the hub set only increases the sum. This proves the exchange.

Let y be the last of the first ⌊3k^δ⌋ primes, so log y∼δ log k. For t≤k set H(t,y)=Σ_{d≤t, P⁺(d)≤y}1/d with 1 included. Uniformly for k/Y≤t≤k, partial summation of the Dickman smooth-number theorem on the bounded range of u=log t/log y gives
$$
 H(t,y)=(\log y)A(\log t/\log y)+o(\log k).
$$
For t≤y the usual harmonic sum gives the contribution to the integral on [0,1], and on [1,1/δ+o(1)] the error is uniform. The all-hub term gives the first summand of C. Exterior squares and higher powers contribute O((log k)Σ_{p>y}1/(p(p−1)))=o(1). The single exterior primes contribute Σ_{y<p≤Y}H(k/p,y)/p. Prime partial summation, or Mertens' estimate in finitely many fixed bins followed by uniform continuity, gives the displayed integral. Since A(u)<∫₀^∞ρ=e^γ for each finite u, this improves the elementary coefficient strictly for each fixed δ. It gives a bound for the full class; attaining it with irreducible sets is open. [Hildebrand and Tenenbaum’s survey](https://tenenb.perso.math.cnrs.fr/PPP/Survey_friables.pdf)
