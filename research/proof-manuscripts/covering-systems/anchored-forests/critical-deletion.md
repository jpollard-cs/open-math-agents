# Sharp logarithmic density at the critical prime cutoff

Codex (OpenAI), November 28, 2026. Written continuation of [marked-prime deletion](marked-prime-deletion.md).

Use the same maximum uncovered density Δ, over all irreducible sets and successful assignments at cap $X=pT$. All primes in an arbitrary mark set are at least p and p is included. The single set of rows deleted is the union of their multiples. Write $N=\log T$ and $v=\log(T/p)$. If
$$
              v\to\infty,\qquad v^2=o(N\log v),
$$
then uniformly over the mark set
$$
         \log\log(1/\Delta)\sim \frac{N\log v}{v}.                       \tag{1}
$$
In particular if $\log(\sqrt X/p)\sim t\sqrt{\log X}$ for fixed t>0, one obtains
$$
 \log\log(1/\Delta)
       \sim \frac1{8t}\sqrt{\log X}\,\log\log X.                          \tag{2}
$$
This is the same cutoff as the exceptional-pair sieve for the minimum. The errors in (1) and (2) are relative errors on the displayed, twice-logarithmic scale.

**Smooth-number input.** For either $a=p$ or $a=\lfloor p/4\rfloor$ the least prime $y(a,T)$ for which $\Psi(T,y)\ge a$ satisfies
$$
                      \log y(a,T)\sim J,\qquad J=N\log v/v.              \tag{3}
$$
Indeed at $y=\exp((1\pm\eta)J)$ for fixed $0<\eta<1$, $u=N/\log y=v/((1\pm\eta)\log v)\to\infty$. Hildebrand's uniform estimate $\Psi(T,y)\sim T\rho(u)$ applies: here $J\gg\sqrt{N}$ for large T, well above $(\log N)^{5/3+\epsilon}$. The classical Dickman estimate $\log\rho(u)\sim-u\log u$ gives $\log(T/\Psi(T,y))\sim v/(1\pm\eta)$. This brackets both thresholds. Let η decrease. These results are from [Hildebrand and Tenenbaum, *Integers without large prime factors*, Theorem 1.1 and the Dickman estimates](https://tenenb.perso.math.cnrs.fr/PPP/Survey_friables.pdf). The given range has $v=o(J)$ and $J=o(N)$.

**Upper bound on lost density.** Since $p=T^{1-o(1)}$, no irreducible period can contain a square of a marked prime for large T, by the highest-digit inequality $q^{e+1}\le X$. Three distinct marked primes cannot occur in one row either. The local-lemma fibre test (1) in [the preceding proof](marked-prime-deletion.md) therefore applies unchanged with $K=\lceil4\sqrt{T+1}\rceil=o(p)$. Every hole lies in an event for a marked prime q at which at least p/2 distinct unmarked cofactor congruences of moduli at most T hit. Work with such an event E of positive density δ.

Condition the uniform integer residue on E in a common period enlarged to contain all primes through T and all cofactor moduli. For each prime l let $m_l$ be the maximum probability of a residue modulo l under this conditional law. Relative entropy with respect to the full uniform law is $\log(1/\delta)$, so CRT, marginalization and entropy subadditivity give
$$
       \log(1/\delta)\ge \sum_{l\le T} D(\mu_l\Vert U_l).
$$
Grouping a heaviest residue versus its complement in each marginal gives $D(\mu_l\Vert U_l)\ge m_l\log(lm_l)-m_l$. Each individual deficit is nonnegative.

Set $\lambda=p/(4T)$ and $w=e^{4v+12}$. Allow all primes at most w and those larger primes up to T with $m_l\ge\lambda$. Each cofactor d containing any disallowed prime has conditional hit probability at most λ. The other cofactors have probability at most one. Taking expectations, at least $p/4$ different integers through T have only allowed prime factors. Compressing the allowed primes in order onto the first equally many primes maps those integers injectively to no larger integers. Consequently the prime at the last rank is at least $y(\lfloor p/4\rfloor,T)$. By the prime number theorem and minimality of the sum of logs on the first primes, the sum of log l on the allowed primes above w is at least $(1-o(1))y(\lfloor p/4\rfloor,T)$, since $\log w=o(J)$. For each such l the marginal deficit is at least $(\lambda/2)\log l$, by the choices of w and λ. Thus
$$
       \log(1/\delta)\ge (1-o(1))\lambda y(\lfloor p/4\rfloor,T)/2
                        =\exp((1+o(1))J)
                   \quad\text{as a lower bound}.
$$
Here $|\log\lambda|=v+O(1)=o(J)$. Summing the density bound over at most X possible marked primes costs $\log X=O(N)$ on the negative-log scale, negligible compared with $\exp((1-o(1))J)$. This proves the required upper estimate for Δ.

**Lower bound on lost density.** Put $y=y(p,T)$ and form M by taking every prime at most y to its greatest power at most T. Every y-smooth integer through T divides M. Choose p divisors of M through T including the highest power of every prime in M; there are enough available and $\pi(y)<p$ by (3). Their lcm is M. On the old digits of M use the $r-1$ ordinary moduli $r^jd$ for $1\le d<r$ at each position $r^j\mid M$, $j\ge1$. Their largest is at most $Ty<pT$ for large T, and all their tests apart from the current digit are earlier. The p terminal rows are p times the selected divisors. The [digit and terminal proof](marked-prime-deletion.md) gives arbitrary-reassignment irreducibility. Marked deletion in the aligned placement leaves exactly the zero class modulo M. Since $\log M\le \pi(y)N$, we have $\log\log M\le\log y+\log N=(1+o(1))J$. This proves (1).

Finally set $L=\log X$ and $w_0=\log(\sqrt X/p)$. Then $N=L/2+w_0$, $v=2w_0$. If $w_0\sim t\sqrt L$, direct substitution gives (2). Although the surviving set is extraordinarily sparse, it may occupy many different residues on any one batch's cofactor period. Controlling that projection, or establishing that the required distribution is possible in a cap-beating irreducible cover, remains the missing step.
