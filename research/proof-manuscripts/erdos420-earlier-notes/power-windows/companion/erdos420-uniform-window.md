# A shorter uniform window for the growth of the divisor count of a factorial

Let \(D(n)=\tau(n!)\), where \(\tau\) counts positive divisors. Put
\[
 c=4411/10000=0.4411,\qquad \delta=1/100000.
\]
For every sufficiently large integer \(n\),
\[
 \log\frac{D(n+\lfloor n^c\rfloor)}{D(n)}\gg n^\delta.
\]
In particular the least number of steps needed for doubling is at most \(\lfloor n^{0.4411}\rfloor\). More precisely, for every sufficiently large real \(x\), at least a constant times \(x^c\) distinct primes greater than \(x^{1-c+\delta}\) divide some integer in \((x,x+x^c]\). The constants do not depend on the starting point.

Erdős, Graham, Ivić and Pomerance proved the corresponding prime statement for \(c=4/9\) and \(\delta=10^{-4}\). This result shortens the window and uses a smaller positive growth exponent. The question in Erdős #420(i) asks for a fixed power of \(\log n\) as window length, and remains open. The same optimization also identifies a barrier near \(0.40980664\) for the particular positivity test used below.

## Prime mass at a single start

Write \(H=x^c\), \(N(d)=\lfloor(x+H)/d\rfloor-\lfloor x/d\rfloor\), and \(b=1-c+\delta\). Summing the factorization identity for every integer in the given interval gives
\[
 \sum_{d\ge1}\Lambda(d)N(d)=H\log x+O(H+\log x).
\]
For \(d\le H\) the sum equals \(cH\log x+O(H)\), by \(N(d)=H/d+O(1)\), Mertens' estimate for \(\sum_{d\le H}\Lambda(d)/d\), and Chebyshev's estimate for \(\sum_{d\le H}\Lambda(d)\). Prime powers \(p^a>H\) with \(p\le H\) contribute \(O(\pi(H)\log(2x))=O(H)\), as each such power has at most one multiple in the interval.

For completeness, higher powers with \(p>H\) also contribute \(o(H)\). Each corresponding integer takes the form \(mp^2\) with \(m\le 2x/H^2\). For any fixed \(m\) the multiples \(mr^2\) in this size range are separated by at least a constant times \(\sqrt x\), greater than \(H\). Each allowable pair \((m,p)\) contributes at most \(\log(2x)\) across the higher powers. Their aggregate is \(O(x^{1-2c}\log x)=o(H)\), since \(c>1/3\). This deals explicitly with powers whose *base* is in the middle range but whose *value* exceeds its upper endpoint.

It follows that
\[
 \sum_{p>x^b}N(p)\log p
 =(1-c)H\log x-\sum_{H<p\le x^b}N(p)\log p+O(H).
\]
A strict saving below \(1-c\) in the normalized middle sum suffices.

## The sieve estimate and its hypotheses

Use the individual-window Selberg upper sieve of Erdős–Graham–Ivić–Pomerance (EGIP), proof of Lemma 3, equations (14)–(19). For \(v=x^u\) with \(c\le u\le b<(1+c)/2\), set \(T(v)=\sum_{v<p\le ev}N(p)\). Dropping higher powers from their sieved set is harmless for this upper bound. Define
\[
 c_0=c-10^{-7},\qquad
 \phi_{k,l}(u)=\frac{c_0(1+k)-k-(l-k)u}{2(1+k-l)}.
\]
For any of the fixed classical or modern exponent pairs in the certificate, take \(z=x^{\phi_{k,l}(u)}\) when \(\phi_{k,l}(u)>0\).

Here are details of the error estimates, in particular the room needed for modern exponent pairs with a subpower loss. The Selberg majorant for \(T(v)\) gives a main term at most \(H/\log z\). EGIP use squarefree weights supported on \(d\le z\), with \(\lambda_1=1\), \(|\lambda_d|\le 1\), and \(\sum_{a,d}\lambda_a\lambda_d/[a,d]\le1/\log z\). After collecting \([a,d]=q\), the weight has absolute value at most \(\tau_3(q)\) and \(q\le z^2\). Every prime counted exceeds \(z\). The approximation to the harmonic sum over the strip contributes at most \(O(Hz^2v^{-1}\log^2(2z))\). For each of the two sawtooth sums, at endpoints \(X=x,x+H\), the reciprocal-phase estimate is
\[
 \left|\sum_{v/q<m\le ev/q}\psi(X/(mq))\right|
 \ll_\epsilon x^\epsilon\!
 \left(x^{k/(k+1)}v^{(l-k)/(k+1)}q^{-l/(k+1)}
                 +\frac{v^2}{xq}\right).
\]
This is the estimate applied in EGIP between (17) and (18), originating in Graham–Kolesnik, Lemma 4.3. To see the compatibility with a modern exponent pair, put \(M=v/q\) and \(F=Xq/v^2\). On a dyadic piece the \(j\)-th Fourier mode of the reciprocal phase has derivative of order \(jF\). Standard exponent-pair control gives \(O_\epsilon(x^\epsilon(jF)^kM^l)\) for \(jF\) bounded below by a sufficiently large constant. The first derivative bound gives \(O(1/(jF))\) when \(jF\) is sufficiently small; in the compact intervening range the second derivative bound gives \(O(\sqrt M)\), covered since \(l\ge1/2\). Truncating the sawtooth sum at height \((M^{1-l}F^{-k})^{1/(1+k)}\) balances the Fourier estimate with \(M\) divided by the height. If that height is smaller than one, the desired first term already dominates \(M\). Standard upper and lower trigonometric approximations at integers handle discontinuities. This yields the displayed bound with all fixed-power logarithms absorbed in \(x^\epsilon\).

Summing the reciprocal-phase estimate over \(q\le z^2\) costs, for each fixed \(\epsilon>0\), at most
\[
 O_\epsilon\!\left(x^\epsilon
 \left[x^{k/(1+k)}v^{(l-k)/(1+k)}
                 z^{2(1+k-l)/(1+k)}+v^2/x\right]\right)
]
after adjusting the harmless input epsilon. The first bracketed term is exactly \(x^{c_0}\). The second has exponent at most \(2b-1<c\). Furthermore
\[
 2\phi_{k,l}(u)-u
 =\frac{c_0(1+k)-k-u}{1+k-l}<0
\]
with uniform slack over this compact strip and the finite list of pairs. This proves \(z^2\ll v x^{-\eta}\) for some fixed \(\eta>0\), bounds the harmonic-sum error, and ensures \(z\le H\) (in fact \(b/2<c\)). Choose the input epsilon small enough for these strict inequalities.

Set \(\Phi(u)=\max_{(k,l)}\phi_{k,l}(u)\). The certificate verifies \(\Phi(b)>0\); each line is nonincreasing, so \(\Phi\) is uniformly positive. For the maximizing pair all the requirements just checked hold. We obtain uniformly throughout the strip
\[
 T(v)\le (1+o(1))\frac{H}{\Phi(u)\log x}.
\]
Cover the middle primes by strips with lower endpoints \(e^j H\) up to \(x^b\), using the entire final strip for an upper bound. Weighting a strip by \(\log(ev)\) and taking the Riemann sum yields
\[
 \sum_{H<p\le x^b}N(p)\log p
 \le H\log x\left(\int_c^b\frac{u}{\Phi(u)}\,du+o(1)\right).
\]
The integrand is continuous and piecewise smooth. Its use takes advantage of the best certified pair separately at each prime size.

## Two certificates for the numerical inequality

The input pairs and their ordinary \(B\)-transforms \((l-1/2,k+1/2)\) are listed in the short executable certificate. There are 37 distinct pairs. The eight explicit inputs are the vertices numbered 0,1,2,3,4,7,8,9 in Table 5.2 of the Analytic Number Theory Exponent Database. The other eleven are Heath–Brown's pairs
\[
 \left(\frac{2}{(m-1)^2(m+2)},1-\frac{3m-2}{m(m-1)(m+2)}\right),\qquad 6\le m\le16 .
\]
The newest published inputs used are the pairs \((89/1282,997/1282)\), \((10769/351096,609317/702192)\), and \((89/3478,15327/17390)\) from Tao–Trudgian–Yang. No unpublished pair or conjectural exponent is used for the uniform result.

On the positive domain of each line, \(u/\phi_{k,l}(u)\) increases, because its numerator derivative after cancellation has the sign of \(c_0(1+k)-k>0\). Equivalently \(u/\Phi(u)\) increases because \(u\) increases and \(\Phi>0\) is nonincreasing. Dividing \([c,b]\) into 32,768 equal pieces, taking right endpoints and rounding each integrand **up** to nine decimal places using integers gives
\[
 c+\int_c^b u/\Phi(u)\,du
 \ \le\ \frac{204787819349075237}{204800000000000000}
 <0.999941 .
\]
The separate analytic check intersects all rational affine lines, selects the upper envelope on each region by its rational midpoint, and joins adjacent identical pieces. On its 23 pieces the integrals of \(u/(a-du)\) are calculated by antiderivative. It bounds the logarithms using their rational atanh-series remainder. The result lies between \(0.999932748493353\) and \(0.999932748493376\). Both checks use only standard-library integer and rational arithmetic for the inequalities.

Consequently \(\sum_{p>x^b}N(p)\log p\gg H\log x\). Each such prime occurs at most once and contributes at most \(\log(2x)\). Distinct primes counted here divide distinct integers because \(2b>1\) and eventually \(x^{2b}>x+H\). Write the corresponding row as \(m=sp\). Then \(s<p\), so the exponent of \(p\) in \((m-1)!\) is exactly \(s-1\). At this step \(D(m)/D(m-1)\ge 1+1/s\). Since \(1/s=p/m\gg x^{b-1}\), summing the logarithms of these \(\gg x^c\) distinct steps proves the claimed lower bound \(\gg x^{c+b-1}=x^\delta\). For integer \(x=n\), the rows of the real interval are exactly the \(\lfloor n^c\rfloor\) required factorial steps.

## A sharp barrier for this particular sieve optimization

Within the preceding test let the error slack and gain exponent tend to zero. Even if the conjectural ideal pair \((0,1/2)\) is allowed, the limiting sieve power on \(c\le u\le1-c\), \(1/3<c<1/2\), cannot beat \(c-u/2\). In fact
\[
 2(1+k-l)(c-u/2)
 -\{c(1+k)-k-(l-k)u\}
 =(c-u)(1-2l)+k(1+c-2u)\ge0.
\]
Here \(k\ge0,\ l\ge1/2\) and \(u\le 1-c\le(1+c)/2\). Equality is attained by the ideal pair. The smallest possible limiting left side in this test is thus
\[
 J(c)=c+\int_c^{1-c}\frac{u}{c-u/2}\,du
 =5c-2+4c\log\frac{c}{3c-1}.
\]
Writing \(r=c/(3c-1)\ge1\), we have \(J'(c)=9+4\log r-12r<0\). The endpoint values are \(+\infty\) at \(1/3\) and \(1/2\) at \(1/2\), as one-sided limits. The unique solution of \(J(c)=1\) lies strictly between \(0.40980664\) and \(0.40980665\), certified by rational logarithm bounds. Strict positivity in the EGIP test is impossible at or below this threshold in its range. For \(c\le 1/3\) its required strip already runs outside the \(v^2/x=o(x^c)\) range. Above the threshold and below \(1/2\), sufficiently small error slack and positive \(\delta\) preserve the strict inequality with a pair sufficiently close to \((0,1/2)\). This is a limitation of the stated middle-prime majorant. It supplies no lower bound for actual worst-case windows.

## Sources, priority and next question

- Erdős, Graham, Ivić and Pomerance, *On the number of divisors of n!* (1996), Lemma 3, equations (9)–(19), Theorem 4 and Corollary 3. The authors suggest that shorter polynomial windows should be obtainable. [Author-hosted paper](https://math.dartmouth.edu/~carlp/factorial.pdf)
- Trudgian and Yang, *On optimal exponent pairs*; Tao, Trudgian and Yang, *New exponent pairs, zero density estimates, and zero additive energy estimates: a systematic approach*. The authors' database supplies exact pairs, their provenance, the \(B\)-process and the subpower-loss convention. [Trudgian–Yang](https://doi.org/10.1090/mcom/3993) · [Tao–Trudgian–Yang](https://doi.org/10.1090/mcom/4138) · [Database, Chapter 5](https://teorth.github.io/expdb/blueprint/exponent-pairs-chapter.html)
- Current statement and the September 2026 work on long intervals of small growth. The latter improves a lower bound for the worst-case doubling time. The sources located in a targeted check did not state the present upper exponent. Priority and external verification remain unconfirmed. [Formal conjectures](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/ErdosProblems/%C2%AB420%C2%BB/) · [2026 lower-bound preprint](https://arxiv.org/abs/2609.15597)
- Replacing the stripwise Selberg majorant by a bilinear prime estimate, or proving a joint constraint on the contributions of different strips, could move the analytic barrier. A polylogarithmic solution would also have to reach a qualitatively shorter scale on every start.
