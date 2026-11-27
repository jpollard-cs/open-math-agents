# Uniform factorial-divisor growth on a window of exponent 0.4354

Let \(D(n)=\tau(n!)\), \(c=2177/5000=0.4354\), \(\delta=1/100000\), and \(b=1-c+\delta=0.56461\). For **every sufficiently large** real \(x\), at least a constant times \(x^c\) distinct primes \(p>x^b\) divide some integer of \((x,x+x^c]\). Consequently, for every sufficiently large integer \(n\),
\[
 \log\frac{D(n+\lfloor n^{0.4354}\rfloor)}{D(n)}
 \gg n^{1/100000}.
\]
In particular the first doubling takes at most \(\lfloor n^{0.4354}\rfloor\) steps. These are unconditional individual-start statements. The polylogarithmic length asked for in Erdős #420(i) remains open.

The companion note gives the uniform exponent \(0.4411\) using exponent pairs alone, and compares it with Erdős–Graham–Ivić–Pomerance's (EGIP) \(4/9\). Here a prime-size interval can use the exponent-pair estimate for its small sieve divisors and Baker–Harman's monomial sum estimate for larger sieve divisors. Both orders of the variables in that estimate matter.

## What the sieve must bound

Use \(H=x^c\), \(N(d)=\#\{x<t\le x+H:d\mid t\}\). As proved in the companion note, for \(1/3<c<1/2\),
\[
 \sum_{p>x^b}N(p)\log p
  =(1-c)H\log x-\sum_{H<p\le x^b}N(p)\log p+O(H).
\]
In particular the treatment of prime powers with base \(p>H\) still applies, since \(1-2c<c\).

Write \(v=x^u\), \(c\le u\le b\), \(T(v)=\sum_{v<p\le ev}N(p)\). We choose a fixed positive divisor-level exponent \(d\) appropriate to a narrow range of \(u\), and put \(z=x^{d/2}\). The Selberg upper weights at this level, as in EGIP equations (14)–(17), satisfy \(\lambda_1=1\), \(|\lambda_j|\le1\), are supported on squarefree \(j\le z\), and satisfy \(\sum_{i,j}\lambda_i\lambda_j/[i,j]\le1/\log z\). Put \(\rho_q=\sum_{[i,j]=q}\lambda_i\lambda_j\), so \(|\rho_q|\le\tau_3(q)=x^{o(1)}\) and \(q\le z^2\). Here and below subpower terms are uniform in the polynomially bounded parameters. Throughout, \(d<u\) with uniform slack, so \(p>v>z\) for every counted prime.

To secure a common short-interval gain for every Fourier mode, choose a nonnegative smooth function \(w\) which is identically one on \([0,1]\), supported on \([-1/\log x,1+1/\log x]\), bounded by one, with integral \(1+O(1/\log x)\), total variation two and \(j\)-th derivative \(O_j((\log x)^j)\). A fixed smooth cutoff rescaled at the two ends has these properties. Majorize the original count by weighting each row \(t\) by \(w((t-x)/H)\), then use the nonnegative square of the Selberg divisor sum. This gives an upper bound for the original sharp interval with no exceptional starts. The resulting main term is
\[
 H\int w\sum_{q\le z^2}\rho_q
           \sum_{v<qm\le ev}\frac1{qm}
 \le (1+o(1))\frac H{\log z}
       +O(H z^2x^{o(1)}/v).
\]
Indeed the inner sum is \(1/q+O(1/v)\), and the displayed harmonic error is negligible because \(d<u\) with slack. We must bound the discrepancies summed over all \(q\).

## Two bounds for the discrepancies

First, the companion exponent-pair estimate applies to smooth row weights with bounded total variation. After summing in \(m\) for fixed \(q\), partial summation integrates the sharp cumulative sawtooth discrepancy against \(w'\); the shifted endpoints remain \(x+O(H)\). The replacement has cost at most a constant. The static exponent-pair level available at a given \(u\) is
\[
 d_0(u)=\max_{(k,l)}\frac{c_0(1+k)-k+(k-l)u}{1+k-l},
 \qquad c_0=c-10^{-7}.
\]
The same 37 established pairs as in the companion note are used. For \(q\le x^{d_0(u)}\), the sum over \(q\) of bounds for the individual discrepancies, with coefficient \(\tau_3(q)\), is \(O(Hx^{-\epsilon_0})\) for some fixed \(\epsilon_0>0\). This follows by the calculation in that note, retaining a subpower loss smaller than \(c-c_0\) and observing \(2b-1<c\). It remains valid on any subset of these \(q\).

For the second bound sit in a dyadic box \(q\asymp x^a\), \(m\asymp x^{u-a}\), so \(qm\asymp v\). Poisson summation in the integer multiplier of \(qm\) writes the discrepancy as a sum of the nonzero terms
\[
 \frac H{qm}\widehat w\!\left(\frac{hH}{qm}\right)
                      e\!\left(-\frac{hx}{qm}\right).
\]
The convention is \(e(t)=\exp(2\pi it)\). The mode zero gives exactly the main term above. For any fixed \(\xi>0\) the tail \(|h|> x^{u-c+\xi}\) costs \(O(x^{-10})\) after all summations, on choosing sufficiently many integrations by parts in \(\widehat w\). Indeed \(qm\asymp v\), and \(|\widehat w(t)|\ll_j (\log x)^j(1+|t|)^{-j}\). The numbers of possible \(q,m\) and all scaling factors are polynomially bounded. Positive and negative modes obey identical estimates.

For completeness, the remaining reductions keep the gain \(H/v\). On each dyadic frequency box, the product cutoff \(v<qm\le ev\) can be separated at logarithmic cost by the elementary truncated Perron formula. Replace both endpoints by half-integers giving the same cutoff for integer \(qm\). The distance of a possible product from the endpoints is then at least \(1/2\). Truncation at \(x^8\) on the line \(\Re s=1/\log x\) has error \(O(vx^{-8})\) per summand. This is negligible after all summations. The separating factors \(q^{it},m^{it}\) have modulus one and can enter the coefficient sequences. Real powers on this integration line are bounded and also separate.

The remaining smooth factor is \((v/(qm))\widehat w(hH/(qm))\). On a dyadic box its mixed partial derivatives with respect to the three variables in normalized coordinates, differentiating at most once per variable, are \(O(x^{3\xi+o(1)})\). To see this, \(hH/(qm)\ll x^\xi\), and each fixed derivative of \(\widehat w\) is bounded by an absolute moment of \(w\), uniformly \(O(1)\). Partial summation in the three variables thus reduces to rectangular subboxes at cost \(x^{3\xi+o(1)}\). The exterior factor is \(H/v\). The coefficients \(\rho_q\) and the number of dyadic boxes cost another \(x^{o(1)}\). We seek a uniform power saving over the trivial target \(v\) in the resulting unweighted-size exponential sum. Dyadic boxes can be split at any change between the available divisor estimates.

## The Baker–Harman input in the full frequency range

Baker and Harman, *Numbers with a large prime factor*, Acta Arith. 73 (1995), Lemma 1, bound
\[
 \sum_{m\sim M}\left|\sum_{j\sim L_1}\sum_{q\sim L_2}
 c_{j,q}\,e(Am^\alpha j^{\alpha_1}q^{\alpha_2})\right|,
 \qquad |c_{j,q}|\le1,
\]
where \(\alpha\ne1\), \(\alpha\alpha_1\alpha_2\ne0\), and \(A>0\).
Set \(L=L_1L_2\) and \(F=AM^\alpha L_1^{\alpha_1}L_2^{\alpha_2}\). Up to squared logarithms the bound is
\[
 L^{13/14} M^{9/14}F^{1/14}+L M^{2/3}
 +L M^{13/12}F^{-1/4}+L^{3/4}M+L^{3/4}M^{1/2}F^{1/4}.
\]
Our outer variable is either \(m\) or \(q\), with exponent \(-1\). The other two exponents are \(-1\) and \(1\), which meet all hypotheses. Positive phase amplitude is obtained by conjugation. All three length parameters lie between 1 and \(O(x)\). A possible isolated index 1 at the bottom of a dyadic range can equivalently be represented by index 2 with the corresponding constant phase rescaling. One-coordinate cutoffs and bounded weights on the outer variable are harmless by the displayed absolute value. The two inner coordinates already allow arbitrary joint bounded weights.

Write \(x^s\) for the frequency length. First take the outer length \(M\asymp x^{u-a}\). Then \(L\asymp x^{s+a}\), \(F\asymp x^{1+s-u}\). Every term of the bound increases with \(s\) after substitution, including the third, whose exponent has coefficient \(3/4\) on \(s\). With ideal terminal frequency \(s=u-c\), the five exponents are all strictly smaller than \(u\) precisely when
\[
 L_*(u)<a<U_*(u),\quad
 L_*(u)=\max\{3(u-c),13u-9c-3\},\quad
 U_*(u)=\min\{(14c-8u-1)/4,\ 3c-2u,\ 4c-u-1\}.
\]
For example the first term gives \(14(u-c)+4a+8u+1<14u\), and the second gives \(a<3c-2u\). Choosing \(q\) as the outer variable supplies the reflected range \(L_*(u)<u-a<U_*(u)\). Strict slack absorbs the slight extension \(s\le u-c+\xi\), partial summations and all logarithms. Thus a divisor exponent in either certified range contributes \(O(Hx^{-\epsilon_1})\) per box after restoring \(H/v\), uniformly at the individual start.

## Exact certificates and the factorial consequence

The first certificate partitions the prime-exponent interval \([c,b]\) into 4,096 equal strips \([l,r]\). In a strip the old level \(d_0(r)\) safely covers all smaller sieve-divisor exponents because each upper-envelope line is nonincreasing. With \(g=10^{-5}\), two further closed intervals of allowed exponents in the whole strip are
\[
 [L_*(r)+g,U_*(r)-g],\qquad
 [r-U_*(r)+g,l-L_*(r)-g].
\]
Indeed \(L_*\) increases and \(U_*\) decreases. Starting from the old interval, append any overlapping allowed interval, repeating once. Truncate the resulting level at \(l-g\). This gives uninterrupted coverage of \([0,d]\) for every \(u\) in that strip. Each of the five affine inequalities has savings at least \(g/12\) in the added intervals before extending the frequency. Their slopes in \(s\) are at most one. Choosing \(\xi=10^{-8}\) covers the extended frequencies and the \(x^{3\xi+o(1)}\) loss. Dyadic constant factors change exponents by \(O(1/\log x)\). The positive slack remains uniform.

Consequently the Selberg estimate in each strip is \(T(v)\le(1+o(1))2H/(d\log x)\). Summing the \(e\)-ratio prime ranges as in EGIP and using the **upper** weighted integrand \(2r/d\) in the whole strip gives
\[
 c+\sum_{[l,r]}(r-l)\frac{2r}{d}
 \le \frac{25583390673365959}{25600000000000000}
 <0.999352 .
\]
This is an exact rational upper bound after upward rounding. The finite number of initial or terminal \(e\)-ratio ranges per strip contributes \(o(H\log x)\) to the weighted sum.

The second checker uses 2,048 different strips. It starts with the five monomials as published, puts \(s=u-c+10^{-8}\), and clips their affine exponents to \(\le u-10^{-6}\) at both endpoints, in each outer-variable orientation. It then computes connected coverage of the divisor interval from zero. It gives the independent upper bound
\[
 \frac{511700563485934523}{512000000000000000}<0.9996 .
\]
The use of both \(u\)-endpoints certifies each entire strip because the inequalities are affine in \((u,a)\). The bound includes the highest frequency and leaves room for all smoothing losses. These are finite certificates for the analytic inequalities in the proof. The asymptotic theorem itself follows by the sieve and the cited exponential-sum results.

The positive margin yields \(\sum_{p>x^b}N(p)\log p\gg H\log x\). Thus \(\gg x^c\) distinct primes occur; each divides a separate row, because \(p>\sqrt{x+H}\). At each such row \(m=sp\), \(s<p\) and the prime raises the divisor count by a factor at least \(1+1/s\). Summing logarithms gives the stated \(\gg x^{c+b-1}=x^\delta\) lower bound.

## What remains after the bilinear improvement

The conditional geometric limit of the original exponent-pair optimization, \(0.40980664\ldots\), persists for this particular enlargement. The second monomial forces \(a<3c-2u\) in the direct orientation; the fourth forces \(u-a>3(u-c)\) in the reflected orientation, hence again \(a<3c-2u\). As \(u\ge c\), both remain under the divisor level \(2c-u\) of the conjectural ideal exponent pair. The companion note proves that even this ideal level reaches the requisite positive middle-prime deficit only above the unique root of \(5c-2+4c\log(c/(3c-1))=1\). A different sum estimate or a different argument for the middle primes is required to cross that threshold.

Baker and Harman's cited paper proves a large-prime statement for square-root windows. Its general Lemma 1, whose coefficients and monomial hypotheses have been checked explicitly above, is the input at the shorter window here. Searches on later large-prime-factor papers, factorial doubling, #420, and the 1996 exponent located no published statement of this particular bound. Its priority and external review remain unconfirmed. No public proof submission has been made.

[Original 1996 factorial-divisor sieve](https://math.dartmouth.edu/~carlp/factorial.pdf) · [Baker–Harman, Lemma 1, p. 121](https://bibliotekanauki.pl/articles/1391261.pdf) · [Tao–Trudgian–Yang, modern exponent pairs](https://doi.org/10.1090/mcom/4138) · [Exponent pairs and their provenance](https://teorth.github.io/expdb/blueprint/exponent-pairs-chapter.html)
