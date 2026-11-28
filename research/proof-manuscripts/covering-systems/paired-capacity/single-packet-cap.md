# A second-order cap bound for one overfilled prime packet

Codex, at the request of Jordan Pollard. AI-authored written proof for review.

Consider the [overfilled packet](overfilled-stars.md) at its exact partition threshold. Write W for its number of right primes, s=t−t/v for the slack at each of them, and P=vW for the product of the surviving left domain sizes. Form the ordinary core first, with distinct primes disjoint from the packet, using r−1 permanent rows at each prime-digit position (r,j), each divisible by rʲ. The permanent core rows have no packet prime factors and leave at least one hole under the covering assignment, as they must in an irreducible cover. Replace its distinguished row by the packet. Allow individual packet rows to be dressed with exterior cofactors or further refined. All final moduli must be distinct, and each must be at most X. Assume v divides t and u=t/v≥2. More generally the following bound holds at u=1 if no final packet row carries two right primes. Write z=√X, and F(z)=Σ_{p≤z}(p−1).

**Throughout this class the number k of distinct moduli satisfies**
$$
                    k\le F(z)+o(z^2/(\log z)^2).
$$
The little-o upper bound is uniform over the choices as X tends to infinity. It permits a smaller positive surplus, including one exceeding the power scale obtained so far in the grouped class. Multiple independent substitutions and simultaneous refinements of earlier core rows using the fresh primes are outside this theorem.

**Finite constraints.** Let Q be the largest right prime and p the largest left prime. Each right vertex q has q+s distinct incident rows. Fix a hole of the permanent core rows. Every tuple of the fresh prime digits is available above it by CRT. Enlarging the assigned packet rows to their raw internal classes gives a saturated-capacity covering assignment there. The private tuples in the refinement argument can likewise be realized above this same hole. By the period-propagation result none of these rows can be divisible by another right prime. Thus q≤z and
$$
       Q+s+W-1\le X/Q,\qquad t\le X/(pQ).
$$
For the first bound, every one of the W−1 other right primes is a forbidden cofactor at Q and is at most Q≤X/Q. For the second, just use the t distinct multiples of pQ. Every left prime pᵢ also has at least pᵢ incident rows, since Wt≥P≥bᵢ. Thus p≤z. A core prime r has r−1 distinct multiples at its first position, so r≤z+1. At a higher position (r,j), rʲ(r−1)≤X. The sum of all higher-position row counts is O(X^(2/3) log X) by taking r=O(X^(1/3)) and j=O(log X). By the exact packet count, the number of rows beyond the sum of first-position costs on all supported primes is at most Ws+W+O(X^(2/3) log X). Using z+1 instead of z in F costs O(z). These errors are o(z²/(log z)²).

Write B=z²/(log z)². If Ws=o(B) the claim follows. To rule out a positive limsup surplus, pass to any sequence with Ws≥εB. When h=1 the only left prime satisfies p≥vW, and Q≥t/v. Therefore Ws≤Wt≤min(pQ,WX/(pQ))≤√(WX)=o(B), as W≤π(z). Hence h≥2. Then t≤Q≤z since the right residual count is (h−1)t+t/v. In particular W≥εz/(log z)², so log W∼log z. The prime number theorem gives Q≥(1−o(1))W log W. Also
$$
 \sum_{r\le p,\ r\ {\rm prime}}\log r\ge\log P\ge\log W.
$$
It follows that p≥(1−o(1))log z. Combining Wt≤WX/(pQ) with Ws≥εB now gives p=O_ε(log z) and Ws=O(B).

**Loss of ordinary primes near z.** Fix a small absolute c>0, for instance 1/4. Left primes below c log z account for at most (c+o(1))log z of the required log product. Thus there are ≫_ε (log z)/(log log z) left primes between c log z and Cε log z. Their reciprocal sum θ is ≫_ε 1/(log log z) and O_ε(1/(log log z)), by the prime-count bound. For any T∼z, the number of integers through T divisible by at least one of them is at least Tθ−O(log z)−Tθ²/2, by two-term inclusion-exclusion. None can serve as a cofactor of a permanent core row at a first-position prime. For any fixed G>0 a core prime r≥z−Gz/log z would have T=floor(X/r)=z+O_G(z/log z) possible cofactors before this exclusion. After it there are fewer than r−1. Therefore every core prime is below z−Gz/log z for each fixed G along this sequence. The left primes themselves are O_ε(log z).

If z−Q is unbounded in units z/log z, pass to a subsequence where it is so, and the entire supported prime set misses the terminal interval of length Gz/log z for every fixed G. Its lost first-position budget is (G+o(1))B by the prime number theorem with classical error term. Since Ws=O(B), this rules out positive surplus on that subsequence.

Otherwise pass to a further subsequence where z−Q=O(z/log z). Now Q∼z, W≤(1+o(1))z/log z and s≤t≤(1+o(1))z/log z. Write a,b for subsequential limits of W log z/z and s log z/z. Both are in (0,1], since Ws≥εB. The finite inequality at Q implies
$$
   z-Q\ge ((a+b)/2-o(1))z/\log z.
$$
The ordinary and left prime bounds above show that the same terminal interval is missed by *all* supported primes. Its budget loss is at least ((a+b)/2−o(1))B, while Ws=(ab+o(1))B. Hence
$$
 \limsup (k-F(z))/B\le ab-(a+b)/2\le0
$$
on this subsequence. The last inequality uses 0≤a,b≤1. These alternatives exclude every positive limsup and prove the assertion.

The analytic input at terminal intervals of length a fixed multiple of z/log z follows directly by subtracting the classical estimate for the prime-counting function and weighting each prime by (1+o(1))z. [De la Vallée-Poussin's prime number theorem](https://encyclopediaofmath.org/wiki/De_la_Vall%C3%A9e-Poussin_theorem).

The proof uses both the missing cofactors of the ordinary rows and the distinct primes forbidden as cofactors on every maximal right fibre. Counting only the surplus indexed rows Ws misses both costs. Further improvement requires handling earlier rows that can use the new primes, more than one interacting packet, or a smaller scale than X/(log X)². The general upper bound here is written and awaits independent review.
