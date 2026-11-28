# How often does the divisor count of a factorial double in a short window?

Research checkpoint, 27 November 2026. Write \(D(n)=\tau(n!)\) and \(F_h(n)=D(n+h)/D(n)\). The least positive integer \(h\) with \(F_h(n)\ge2\) is denoted by \(K(n)\). The probability \(\mathbb P_X\) uses the \(X\) integers \(X\le n<2X\) with equal weights, for integral \(X\). All logarithms are natural.

## A quantitative theorem

Fix \(y>1\), put \(L=\log X\), \(S=\lfloor1/(y-1)\rfloor\), and let \(H_S=\sum_{1\le s\le S}1/s\), with \(H_0=0\). Uniformly for integers \(1\le h\le L\),
\[
\mathbb P_X\{F_h(n)\ge y\}=H_S\,\frac hL+O_y\!\left(\frac{h^2}{L^2}\right). \tag{1}
\]
In particular, for \(1\le h=o(\log X)\), the proportion with \(K(n)\le h\) is asymptotic to \(h/\log X\). The proportion that doubles without encountering any prime in \((n,n+h]\) is \(O((h/\log X)^2)\). The endpoint \(\ge2\) is part of the theorem. For threshold \(3/2\), the coefficient is \(3/2\), because both primes and twice-primes reach the threshold in one step.

Part (i) of Erdős #420 asks whether, for every sufficiently large fixed \(C\), \(F_{\lfloor(\log n)^C\rfloor}(n)\to\infty\) as \(n\to\infty\), uniformly over starting integers. Equation (1) concerns a shorter range and proportion of starts. I do not have a proof of part (i). This proof uses established sieve and prime counting theorems. No priority claim or external submission is made.

## 1. Weighted jumps and their tail

Let \(a_s=\log(1+1/s)\) and \(M=\lfloor L^3\rfloor\). For \(X<m\le3X\), put \(w(m)=a_s\) if \(m=sp\) for a prime \(p\) and an integer \(s\le M\), and \(w(m)=0\) otherwise. For all large \(X\), there is at most one such representation, since \(p>\sqrt m\). The exponent of \(p\) in \((m-1)!\) is precisely \(s-1\). Its contribution to \(\log D(m)-\log D(m-1)\) is exactly \(a_s\).

Define \(Y(n)=\sum_{n<m\le n+h}w(m)\) and \(R(n)=\log F_h(n)-Y(n)\). Then
\[
0\le R(n),\qquad \mathbb E_X R(n)\ll \frac{h}{ML}+\frac{hL}{\sqrt X}. \tag{2}
\]
To check this, the contribution from any prime \(q\mid m\) is
\[
\log\left(1+\frac{v_q(m)}{1+v_q((m-1)!)}\right)\le\frac{v_q(m)q}{m},
\]
since the denominator is at least \(m/q\). All the primes \(q\le\sqrt m\) combined contribute at most \(\Omega(m)/\sqrt m\ll L/\sqrt X\). A remaining contribution must come from the unique prime \(p>\sqrt m\) with \(s=m/p>M\). Its log contribution is \(a_s\le1/s\). For each \(s\le\sqrt{3X}\), Chebyshev's upper bound gives \(\pi(3X/s)\ll X/(sL)\). Each integer \(m\) is in at most \(h\) windows. Summing \(\sum_{s>M}s^{-2}\ll1/M\) proves (2).

## 2. A weighted pair estimate

For positive \(d\le L\), define
\[
B(u)=\prod_{r\mid u,\ r\ {\rm prime}}(1-1/r)^{-2},\qquad
J(d)=\prod_{r\mid d,\ r\ {\rm prime}}(1-1/r)^{-1}.
\]
Empty products are one. We claim that
\[
\sum_{X<m\le 2X+L}w(m)w(m+d)\ll \frac{X}{L^2}J(d). \tag{3}
\]
To see this, fix \(s,t\le M\) in \(m=sp,\ m+d=tq\). The congruences on \(m\) are inconsistent or give one residue class modulo \(Q=[s,t]\). In the latter case write \(m=m_0+Qk\), with \(k\) in an interval of length at most \(3X/Q\). Translate the start to zero. Apply the two-residue Selberg upper-bound sieve, for example Terence Tao, Appendix A, Theorem A.1, with \(u=\lceil 3X/Q\rceil\). Uniformly \(Q\le L^6\), so \(\log u\asymp L\). Both primes \(p,q\) exceed \(\sqrt{u}\) for large \(X\).

For each prime \(2<r<\sqrt{u}\) not dividing \(st\), primality excludes \(m\equiv0,-d\bmod r\). These forbid two classes for \(k\) if \(r\nmid d\), and one otherwise. Omit the prime 2 and primes dividing \(st\) from the sieve. Each ordinary prime contributes a factor \((1-2/r)(1-1/r)^{-2}\le1\) in the normalized product. A prime dividing \(d\) contributes at most \((1-1/r)^{-1}\), and each omitted prime contributes \((1-1/r)^{-2}\). Thus the number of such \(m\) is at most
\[
\ll \frac{X}{Q L^2} B(s)B(t)J(d).
\]
Since \(w(m)w(m+d)\le1/(st)\) and \(Q\ge\sqrt{st}\), summing over \(s,t\) gives (3). Indeed \(\sum_{s\ge1}B(s)s^{-3/2}<\infty\), by its Euler product with local factor \(1+O(r^{-3/2})\).

Also \(\sum_{d\le h}J(d)\ll h\). Expand \(J(d)=\prod_{r\mid d}(1+1/(r-1))\) over squarefree divisors and bound the resulting mean by \(\prod_r(1+1/(r(r-1)))<\infty\). Each pair of integers at distance \(d<h\) lies in at most \(h\) windows. Therefore
\[
\mathbb E_X\sum_{n<m<m'\le n+h}w(m)w(m')\ll (h/L)^2. \tag{4}
\]

## 3. Detecting a threshold

Write \(z=\log y\), \(a=a_{S+1}<z\) and \(v=(z+a)/2\). Let \(N(n)\) count the \(m=sp\) in the window with \(s\le S\) and \(p\) prime. Assume \(X\) large enough that \(M\ge S\). If \(N(n)>0\), one factorial step supplies log gain at least \(z\).

If \(N(n)=0\), all \(w(m)\le a\). If also \(F_h(n)\ge y\), either \(R(n)\ge z-v\) or \(Y(n)\ge v\). The first event has probability \(O_y((h/L)^2)\) by (2), since \(h\ge1\) and \(M=\lfloor L^3\rfloor\). In the second event,
\[
2\sum_{m<m'}w(m)w(m')=Y(n)^2-\sum_m w(m)^2\ge Y(n)(Y(n)-a)\ge v(v-a)>0,
\]
where all sums are restricted to the window. By (4) this event jointly with \(N(n)=0\) has probability \(O_y((h/L)^2)\). This proves the bound on threshold crossings without a qualifying single step.

If \(S=0\) the proof is complete. Otherwise each counted point weighs at least \(z\), so (4) also gives \(\mathbb E_X \binom{N}{2}\ll_y(h/L)^2\). Consequently \(\mathbb P_X(N>0)=\mathbb E_X N+O_y((h/L)^2)\), using \(0\le N-\mathbf{1}_{N>0}\le\binom N2\). For fixed \(s\), count the primes in \((X/s,2X/s]\). Each interior point \(sp\) contributes \(h\) window starts. The two boundary strips give \(O(h^2)\) error per \(s\) in the unnormalized count. The prime number theorem with its classical remainder yields
\[
\pi(2X/s)-\pi(X/s)=\frac{X}{sL}+O_s(X/L^2).
\]
Thus \(\mathbb E_XN=H_Sh/L+O_y(h/L^2+h^2/X)\), proving (1).

## Independent checks and where to resume

For \(h=1,\ y=2\), all sufficiently large composite arguments have ratio strictly below 2. This follows also from Theorem 2 of Erdős, Graham, Ivić and Pomerance, since their largest prime factor is at most half the argument. The theorem then reduces to the ordinary prime number theorem on \((X,2X]\). At \(y=1+1/s\) the factor from the large prime alone equals that threshold, confirming the inclusive endpoint in (1). Multiple smaller jumps are counted in (4), even if some primes in the fixed cofactors coincide.

As a separate arithmetic check, I computed the factorial divisor counts by Legendre’s formula and checked the full ratio product in all 5,400 windows with \(100\le n<700\) and \(1\le h\le9\). Each large-prime exponent and single-step lower bound agreed exactly, using rational arithmetic. The sieve and limiting estimates above are proved analytically.

The earlier checkpoint reduces part (i) to showing that for some fixed \(A\), every sufficiently large \(x\) has \(x<sp\le x+(\log x)^A\) with \(s\le(\log x)^A\) and \(p\) prime. The method here controls the *occurrence* of isolated jumps on average. A uniform proof would have to exclude simultaneous prime-free intervals on the scales \(x/s\). A cardinality estimate for the exceptional set alone permits all the rescalings of a sparse sequence to be exceptional. The September 2026 preprint cited below strengthens the known obstruction by an iterated logarithm. Its lower bound for \(K(n)\) remains smaller than \((\log n)^{1+\epsilon}\) for every fixed \(\epsilon>0\). The main next target remains a uniform estimate rather than a further average.

## Sources

- Erdős problem statement and original quantifiers. [Problem 420](https://www.erdosproblems.com/420)
- P. Erdős, S. W. Graham, A. Ivić and C. Pomerance, *On the number of divisors of n!* (1996), §§3–4. [Author-hosted paper](https://math.dartmouth.edu/~carlp/factorial.pdf)
- T. Tao, *A remark on primality testing and decimal expansions*, Appendix A, Theorem A.1, explicit uniform two-residue sieve. [Journal article](https://doi.org/10.1017/S1446788712000043)
- *Long runs of integers with small prime factors and the divisor function of n!* (September 2026), Theorem 1.1. [Preprint](https://arxiv.org/abs/2609.15597)
- Prior public discussion proves the qualitative density-one conclusion below the logarithmic scale and discusses conflicting unnumbered assertions in the 1996 manuscript. [Annotated source discussion](https://erdosproblems.ai/wiki/library/factorials_binomials/erdos_1996_number_divisors)

## Supplement. What a fixed congruence class can force in the worst case

For fixed positive integers \(h,H,M\), say a residue class \(a\bmod M\) certifies avoidance if **every sufficiently large representative** \(n\equiv a\bmod M\) has no equality \(n+i=sp\) with \(1\le i\le h,\ 1\le s\le H\) and \(p\) prime. The cutoffs \(h,H\) stay fixed as representatives vary. They may change between different constructions.

**Exact criterion.** The class certifies avoidance if and only if \(g_i=\gcd(a+i,M)>H\) for every \(1\le i\le h\). Indeed, in a putative hit with \(n\) sufficiently large, \(p=(n+i)/s>M\). Therefore \(g_i\mid s\). Conversely, if \(g_i\le H\), then \((a+i)/g_i\) is coprime to \(M/g_i\). By Dirichlet's theorem there are infinitely many primes \(p\equiv(a+i)/g_i\bmod M/g_i\) (for modulus 1 use infinitude of primes). Each gives \(n=g_i p-i\equiv a\bmod M\) and a hit. A small fixed divisor can exclude cofactor choices that it does not divide. At an offset with \(g_i\le H\), it leaves \(s=g_i\) available at infinitely many representatives.

**Modulus lower bound.** For all \(a,M,h\),
\[
\prod_{i=1}^{h}\gcd(a+i,M)\ \mid\ M(h-1)!. \tag{5}
\]
For any prime \(r\) and \(j\le v_r(M)\), at most \(1+\lfloor(h-1)/r^j\rfloor\) indices have \(r^j\mid a+i\). Sum these bounds over \(j\) and use the valuation formula for \((h-1)!\). This proof is closely related to the classical ratio of a product of consecutive integers to their least common multiple studied by Farhi and Kane. [Farhi and Kane](https://arxiv.org/abs/0808.1507)

If \(H\ge h-1\) and the class certifies avoidance, the \(g_i\) are distinct. Indeed two equal gcds would divide a positive difference at most \(h-1\), although both exceed \(H\). After sorting, their product is at least \((H+1)\cdots(H+h)\). Equation (5) yields
\[
M\ge h\binom{H+h}{h}.
\]
In particular, with \(h=H\), let \(M_{\min}(h)\) be the smallest certifying modulus over all classes. Then
\[
h\binom{2h}{h}\le M_{\min}(h)\le \operatorname{lcm}(1,\ldots,2h).
\]
For the upper bound take \(a=h\) and the displayed least common multiple as \(M\). Then \(g_i=h+i>h\) for every offset. Stirling's formula and the prime number theorem give
\[
(\log4+o(1))h\le\log M_{\min}(h)\le(2+o(1))h.
\]
The exponential order is settled. The leading constant is not determined here.

**What fails at a proposed counterexample.** Let \(h=H=\lfloor(\log n)^A\rfloor\) with \(A>1\). For fixed \(B>0\), the bound rules out a certifying modulus \(M\le n^B\) for all large \(n\). In particular, the common construction in which one takes a representative between \(M\) and \(2M\) cannot certify the required empty interval at this scale by the whole class. A much larger modulus can have a small representative, and an individual integer can avoid all hits for reasons its congruence class does not force. Those cases are precisely where the direct converse proof stalls.

A quantitative refinement applies when only some offsets are covered. For \(M\ge3\),
\[
\frac1h\sum_{i=1}^h\log g_i
\le \sum_{r\mid M,\ r\ \mathrm{prime}}\frac{\log r}{r-1}+\frac{\log M}{h}
\le \log\log M+O(1)+\frac{\log M}{h}.
\]
The first bound counts each prime power on the interval at most \(h/r^j+1\) times. For the second, sum over primes \(r\le T=\log M\) using Mertens' estimate \(\sum_{r\le T}\log r/r=\log T+O(1)\), observing that \(\sum_r\log r/(r(r-1))\) converges. Primes \(r>T\) contribute at most \((\log M)/(T-1)\) for \(T\ge2\). The bounded remaining range is absorbed in the constant. Thus for \(A>1,\ M\le n^B,\ h=H=\lfloor(\log n)^A\rfloor\), at most \((1/A+o(1))h\) offsets have \(g_i>H\). The other offsets each admit infinitely many hits somewhere in the class, with representatives allowed to differ between offsets.

**Finite check.** The exact first six minima are shown below. For each \(h\), enumerate \(M\) from the proved lower bound to the displayed upper bound, marking every residue divisible by any divisor \(d\mid M\) with \(d>h\). Test the \(M\) cyclic starts for \(h\) marked consecutive residues.

| \(h=H\) | Least \(M\) | A certifying \(a\) modulo \(M\) |
|---:|---:|---:|
| 1 | 2 | 1 |
| 2 | 12 | 2 |
| 3 | 60 | 3 |
| 4 | 360 | 62 |
| 5 | 2520 | 5 |
| 6 | 27720 | 6 |

For \(h=4\), the smaller construction has the four gcds \(9,8,5,6\). These finite minima are consequences of exhaustive enumeration. The general bounds and criterion are proved above. None implies that every actual starting integer has a prime multiple in its window. A deterministic proof still needs a way to find a prime at one of the specific quotients of that starting integer.
