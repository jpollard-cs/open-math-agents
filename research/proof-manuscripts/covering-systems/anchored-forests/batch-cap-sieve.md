# The square-root threshold for joint batch visibility

Codex (OpenAI), November 28, 2026. AI-authored written research on the minimum largest modulus in Erdős #1189(ii).

The [joint batch inequality](batch-cap.md) gives a restriction on **every** irreducible cover below the proposed leading scale for its greatest modulus. No separation assumption on the prime factors of the cover is needed. The threshold obtained here is for the proof's sieve. Its optimality for irreducible systems is open.

Let X be the largest of k distinct moduli in an irreducible covering set, $L=\log X$, $F(t)=\sum_{p\le t}(p-1)$. Reserve any modulus. Choose $1\le u\le L/8$ and write $Y=\sqrt X\exp(-u)$. Set aside the following rows before forming batches:

1. rows divisible by the square of their largest prime;
2. rows with two different prime factors greater than Y.

For each remaining largest prime q, partition its rows into complete batches of q in any fashion, leaving fewer than q unbatched. For one dyadic bin $Q\le q<2Q$, consider all of its complete batches. Fix all the other nonreserved rows, including the set-aside rows, in a **common** residue assignment. For a complete batch B let $b_B$ count the residues of the resulting holes modulo $\operatorname{lcm}_{n\in B}(n/q)$. Let $V_Q$ be the minimum of $\max_B b_B$ over those assignments in this bin. Empty bins have $V_Q=1$. Write $V=\max_Q V_Q$. These minima exist by periodicity.

**Unconditional tradeoff.** Uniformly in the cover, reservation, partition and u,
```math
  k\le 1+F(\sqrt X)+E(X,u)+O(X/L^3)+O(X V e^{-u}),                \tag{1}
```
where
```math
 E(X,u)=\sum_{Y<p<q\le\sqrt X}\left\lfloor\frac X{pq}\right\rfloor
 \ll \frac{X(u+1)^2}{L^2}.
```
In particular along any sequence with $k\ge F(\sqrt X)+cX/L$ for a fixed $c>0$, take $u=t\sqrt L$ for any fixed $0<t<\sqrt{c/2}$. Then
```math
                V\gg_{c,t}\frac{\exp(t\sqrt L)}{L}.                \tag{2}
```
This means that for **every** partition there is a bin such that **every** assignment to the other rows leaves at least one batch in it seeing this many residues. The choice of batch can depend on the assignment. All of that batch's cofactors have prime factors at most $\sqrt X\exp(-t\sqrt L)$. If $X\le(1-\epsilon)k\log k$ on an unbounded sequence, then any fixed $c<\epsilon/(1-\epsilon)$ is admissible eventually, since $X\ge k+1$ and $F(\sqrt X)\sim X/L$.

**Bound for a class.** Suppose a family admits reservations and partitions with $V\le B(X)$ for the single cutoff $u=\log B(X)+2\log L$, with $B(X)\ge1$ and $\log B(X)=o(\sqrt L)$. Then
```math
 k\le F(\sqrt X)+O\!\left(\frac{X(\log B(X)+\log L)^2}{L^2}\right)
       =(1+o(1))\frac X{\log X}\quad\text{as an upper bound}.          \tag{3}
```
The explicit [prime-stage examples](batch-cap.md) attain the leading constant along their sizes. They have at most $q-1$ rows left per first-position group after their reservation; thinning cannot create complete batches. The bound allows arbitrarily many prime factors in a cofactor and arbitrary exceptional rows, subject to genuine irreducibility. A polylogarithmic B gives error $O(X(\log\log X)^2/(\log X)^2)$ above F. This is stronger than applying a separate bounded-visibility estimate to each prime without sharing assignments inside a bin.

**Proof.** At the highest q digit occurring in a covering assignment, the moduli that do not test that digit leave a hole. They form a proper subset. Varying the digit above this hole requires at least q distinct moduli divisible by the corresponding prime power. In particular every prime in this cover is at most $\sqrt X$.

For the first set-aside class, integers whose largest prime is at most $L^3$ number at most
```math
       X^{5/6}\prod_{p\le L^3}(1-p^{-5/6})^{-1}
       \le X^{5/6}\exp(O(\sqrt L))=o(X/L^3).
```
Indeed $\sum_{m\le L^3}m^{-5/6}=O(\sqrt L)$, and the product is just the geometric-series bound for smooth integers. Squares of primes $p>L^3$ divide at most $X\sum_{m>L^3}1/m^2=O(X/L^3)$ integers. This pays for every higher-position row.

For the second set-aside class, $Y\ge X^{3/8}$ and three primes above Y, counted with multiplicity, already exceed X. For each distinct pair $Y<p<q\le\sqrt X$ every multiple up to X has these as its two largest prime factors, and no such multiple belongs to another pair. Thus E is the exact full arithmetic count for pairs in this interval. Summing $1/p$ in fixed-ratio bins using $\pi(s)\ll s/\log s$ gives $\sum_{Y<p\le\sqrt X}1/p\ll(u+1)/L$. This proves the uniform bound.

For the leading constant at the critical cutoff, if $u\to\infty$ and $u=o(L)$, partial summation of the prime number theorem uniformly above Y gives
$\sum_{Y<p\le\sqrt X}1/p=(2+o(1))u/L$.
The endpoint terms are $O(1/L)=o(u/L)$ and the main integral is $\log((L/2)/(L/2-u))$. The diagonal reciprocal-square sum is $O(1/Y)$. Rounding all $X/(pq)$ down costs at most $\pi(\sqrt X)^2=O(X/L^2)$. Hence
```math
                          E(X,u)=(2+o(1))Xu^2/L^2.                          \tag{4}
```
This exact leading count explains the constant in (2). An upper bound replacing E by all such integer multiples cannot discard this term at $u\asymp\sqrt L$.

Every surviving batch cofactor uses only primes at most Y: if $q>Y$ this follows from both exclusions, and if $q\le Y$ it follows from the largest-prime rule. The joint log-pattern count for the whole bin is at most $\pi(Y)L\ll Y$, because each cofactor is at most X and $\log Y\ge3L/8$. Use the assignment attaining $V_Q$. By the joint batch inequality there are $O(V_QY)$ batches there. Each uses fewer than 2Q rows. Summing over dyadic Q costs $O(\sqrt X VY)$, since the *sum* of these powers of two is $O(\sqrt X)$. The leftovers total at most $F(\sqrt X)$. Adding the reserved row and set-aside counts proves (1). Equations (2) and (3) follow by substitution, using (4) for the constant in (2).

These results leave open whether every irreducible family admits sufficiently small simultaneous projections, or whether a family with large projections beats the leading cap. A particularly concrete next step is to use some of the set-aside $pqd$ rows in the **same** reassignment: their remaining factor satisfies $d\le e^{2u}$, and the pair $p,q$ is unique. Bounding just their total number has the limitation in (4).

The [integer and arithmetic checks](batch-sieve-check.py) independently enumerate the exceptional rows and the dyadic projections on small covers. The finite product inequality used in the proof has [a kernel-checked formalization](JointBatch.lean). The sieve, threshold and asymptotics here are written proofs.
