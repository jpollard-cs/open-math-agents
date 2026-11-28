# Erdős #420(i) and the explicit formula at an individual starting integer

27 November 2026. The open question asks whether the divisor count of \(n!\) grows by an unbounded factor between \(n\) and \(n+\lfloor(\log n)^C\rfloor\) for some fixed \(C\), at every sufficiently large \(n\). The previous checkpoint reduces this to finding at least one \(sp\in(x,x+h]\) with \(p\) prime and \(s\le Q\), for some fixed polylogarithmic bounds on \(h,Q\) at every \(x\). This note examines an attempted proof by averaging Chebyshev's explicit formula over the possible \(s\).

## Result

Uniformly for \(1\le h,Q\le(\log x)^B\), for each fixed \(B>0\), let \(Q\) be integral, \(H_Q=\sum_{s\le Q}1/s\), and let \(w_s\ge0\) be arbitrary with \(W=\sum_{s\le Q}w_s/s>0\). The explicit formula for
\[
\sum_{s\le Q}w_s\{\psi((x+h)/s)-\psi(x/s)\}
\]
has main term \(hW\). The sum of the absolute values of its individual nontrivial-zero terms, **on just the positive ordinates \(x/(4h)<\gamma\le x/(2h)\)**, satisfies
\[
\frac1{hW}
\sum_{x/(4h)<\gamma\le x/(2h)}
\left|\frac{(x+h)^\rho-x^\rho}{\rho}
       \sum_{s\le Q}w_s s^{-\rho}\right|
\gg \frac{\sqrt{x}\log x}{hQ\sqrt{H_Q}}. \tag{1}
\]
Zeros are counted with multiplicity. The bound is unconditional and diverges for every fixed polylogarithmic pair of cutoffs. Thus a proof by absolute termwise control of the unsmoothed explicit formula cannot yield positivity on these windows, even with cofactors combined before taking absolute values. Bounds that retain cancellation between distinct zeros remain possible. No zero-free or prime-free interval is proved.

The same conclusion holds for any common nonnegative smooth weight within the window. If each cofactor is allowed its own nonnegative smooth weight, the right-hand side becomes \(\gg\sqrt{x}\log x/(hQ^3\sqrt{H_Q})\), still divergent. The statements only concern these pointwise triangle-inequality arguments. A shorter truncation would need a separate pointwise treatment of the omitted zeros or truncation error.

## A mean value on reflected pairs of zeros

Let \(A(z)=\sum_{s\le Q}w_s s^{-z}\), \(E=\sum w_s^2/s\), \(U=\sum w_s\). For \(T\to\infty,\ 1\le Q\le(\log T)^b\) with fixed \(b\), let \(\mathcal Z_T\) denote the zeros \(T<\operatorname{Im}\rho\le2T\). The functional equation pairs \(\rho\) with \(\rho^\ast=1-\overline{\rho}\) in this same band. Then
\[
\Re\sum_{\rho\in\mathcal Z_T} A(\rho)\overline{A(\rho^\ast)}
=(1+o(1))|\mathcal Z_T|E. \tag{2}
\]
The relative error is uniform in the coefficients, which can also be real with either sign if \(U\) is replaced in estimates by \(\sum|w_s|\).

Indeed, expanding gives terms \((w_sw_t/t)\sum_{\rho\in\mathcal Z_T}(t/s)^\rho\). The diagonal contributes \(|\mathcal Z_T|E\). For \(1\le s<t\le Q\), Gonek's uniform Landau formula gives
\[
\sum_{\rho\in\mathcal Z_T}(t/s)^\rho
=-\frac{T}{2\pi}\Lambda(t/s)+O\big(Q^2\log^2(2QT)\big).
\]
Here \(\Lambda(u)\) vanishes except at integral prime powers. In Theorem 1 of the cited paper, the distance from \(t/s\) to a different prime power is at least \(1/Q\), and \(\log(t/s)\ge 1/Q\), so the stated coarse remainder is sufficient. Reflection of zeros converts the reverse pair \(t<s\) into the complex conjugate of its already weighted forward term. The real off-diagonal main contribution is
\[
-\frac{T}{\pi}\sum_{ks\le Q,\ k\ge2}
           \frac{\Lambda(k) w_s w_{ks}}{ks}
=O(T\log(2Q) E).
\]
To bound it, use \(2|w_s w_{ks}|\le w_s^2+w_{ks}^2\), then \(\sum_{k\le Q}\Lambda(k)/k\ll\log(2Q)\) and \(\sum_{k\mid m}\Lambda(k)=\log m\). For the accumulated remainder, Cauchy–Schwarz gives \(U\le\sqrt{\sum_{s\le Q}s}\sqrt E\le Q\sqrt E\) and \(W\le\sqrt{H_Q E}\). Hence the sum of the absolute errors is \(O(Q^3\sqrt{H_Q}\log^2(2QT)E)\). Both errors are \(o(|\mathcal Z_T|E)\), since the Riemann–von Mangoldt count is \(|\mathcal Z_T|\sim T\log T/(2\pi)\). This proves (2). [Gonek, *A formula of Landau and mean values of ζ(s)*, Theorem 1](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf)

Write \(\mathcal Z_T^+=\{\rho\in\mathcal Z_T:\Re\rho\ge1/2\}\). In each reflected pair, the factor on the left half is at most \(U\) in modulus. Counting both members of a pair, with a harmless factor of two for zeros on the line, (2) therefore implies
\[
\sum_{\rho\in\mathcal Z_T^+}|A(\rho)|
\gg |\mathcal Z_T|E/U
\ge |\mathcal Z_T|\frac{W}{Q\sqrt{H_Q}}. \tag{3}
\]
This use of reflected pairs avoids assuming that all nontrivial zeros have real part \(1/2\).

## The pointwise zero terms

Choose \(T=x/(4h)\). For \(\rho=\beta+i\gamma\in\mathcal Z_T^+\), the phase \(\gamma\log(1+h/x)\) is bounded above and below by fixed positive constants smaller than 1 for all large \(x\). Thus
\[
\left|\frac{(x+h)^\rho-x^\rho}{\rho}\right|
=\frac{x^\beta|e^{\rho\log(1+h/x)}-1|}{|\rho|}
\gg hx^{\beta-1}\ge h/\sqrt{x}.
\]
Combining this estimate with (3) proves (1). The classical explicit formula uses half weight at a prime power endpoint. One can take the two endpoints \(x+1/2,x+h+1/2\) for integer \(x,h\) to count the original integers \(sp^k\in(x,x+h]\) with full weights. Division by any integer \(s\) leaves a noninteger endpoint. The replacement changes the estimates by a \(1+o(1)\) factor.

For a common nonnegative continuous taper \(g\) supported in \([x,x+h]\), with integral \(I>0\), the Mellin kernel is \(\int g(y)y^{\rho-1}\,dy\). After factoring out \(x^{i\gamma}\), every phase \(\gamma\log(y/x)\) stays in \([0,1/2]\) on the same band. Its real part after rotation is therefore \(\gg I x^{\beta-1}\). For a smooth taper this is the kernel of the smoothed explicit formula. Replacing \(h\) by \(I\) in the kernel and main term proves the same ratio.

For cofactor-dependent nonnegative smooth tapers \(g_s\) set \(w_s=\int g_s(y)\,dy\), so \(W=\sum w_s/s\) is now the main term. Choose \(T=x/(D hQ^2)\) with a sufficiently large absolute constant \(D\). Factor \(x^{\rho-1}\) from the zero term. Its remaining coefficient is
\[
A(\rho)+e_\rho,\qquad
|e_\rho|\ll \frac1{D Q^2}\sum_{s\le Q}\frac{w_s}{\sqrt s}
\le \frac{\sqrt{QE}}{D Q^2}\,O(1)
\quad(\rho\in\mathcal Z_T^+).
\]
This follows from \(|(y/x)^{\rho-1}-1|\ll|\rho-1|h/x\ll1/(DQ^2)\). The total of these error bounds is at most a fixed small fraction of the lower bound \(\gg|\mathcal Z_T| E/U\) when \(D\) is chosen large, since \(U\le Q\sqrt E\). Thus \(\sum_{\rho\in\mathcal Z_T^+}|A(\rho)+e_\rho|\gg |\mathcal Z_T|W/(Q\sqrt{H_Q})\). Multiplying each nonnegative modulus by \(|x^{\rho-1}|\ge1/\sqrt x\) yields the claimed ratio \(\gg\sqrt{x}\log x/(h Q^3\sqrt{H_Q})\).

## Higher prime powers and the remaining target

A positive lower bound for the von Mangoldt sum counts prime powers as well as primes. For the untapered sum, powers \(p^k\) with \(k\ge2\) contribute \(O(U\log x\log\log x)\), uniformly in the chosen window. For fixed \(s,k\), consecutive \(k\)-th powers in \([x/s,(x+h)/s]\) have spacing \(\gg\sqrt{x/Q}\) if two occur, by the mean-value theorem, while this interval has length at most \(h\). Hence at most one occurs. Its weight is at most \(w_s\log(2x)/k\). Sum this over \(2\le k\le \log(2x)/\log2\) and over \(s\). In particular, with all \(w_s=1\), a uniform lower bound of order \(hH_Q\) would produce a genuine prime hit whenever \(hH_Q/(Q\log x\log\log x)\to\infty\). This prime-power error can be made negligible by choosing the exponent of the window larger than that of the cofactor cutoff.

The missing ingredient is a lower bound at each individual \(x\) for the prime sum, or a bound on the **signed** explicit-formula error beating the positive main term there. The estimates above identify a necessary cancellation if the explicit-formula route is pursued. They supply neither this signed bound nor a counterexample to Erdős #420(i). No external submission or priority claim has been made.
