# Short intervals in which the divisor count of a factorial grows

Let \(D(n)=\tau(n!)\), let \(h_C(n)=\lfloor(\log n)^C\rfloor\), and put \(G(n,h)=\log(D(n+h)/D(n))\). All logarithms are natural. Part (i) of Erdős problem 420 asks whether \(G(n,h_C(n))\to\infty\) for all sufficiently large fixed \(C\). Monotonicity in \(h\) makes this equivalent to the existence of one such \(C\). [Problem statement](https://www.erdosproblems.com/420)

We give an equivalent arithmetic condition for growth at every sufficiently large start. We also prove unconditionally that, on a set of integers of natural density one, \(G(n,h_{2.1}(n))\gg(\log n)^{1/20000}\). The all-start condition remains open. No priority is claimed for these deductions.

## 1. A uniform truncation by the cofactor

For positive integers \(h,Q\), write
\[
a_s=\log(1+1/s),\qquad
W_Q(n,h)=\sum_{s=1}^Q a_s\left(\pi((n+h)/s)-\pi(n/s)\right).
\]
For all integers \(n\ge16\), \(h\ge1\), and \(1\le Q\le\sqrt n\),
\[
0\le G(n,h)-W_Q(n,h)
\le h\log\left(1+\frac1{Q+1}\right)+\frac{2h}{\sqrt n}. \tag{1}
\]

To see this, fix \(n<m\le n+h\). For each prime \(p\mid m\), its contribution to \(\log D(m)-\log D(m-1)\) is
\[
\log\left(1+\frac{v_p(m)}{1+v_p((m-1)!)}\right)\le\frac{v_p(m)p}{m},
\]
since the first \(m/p-1\) multiples of \(p\) occur in \((m-1)!\). For \(2\le p\le\sqrt m\), one has \(p/\log p\le\sqrt m/\log\sqrt m\). Indeed, \(u/\log u\) decreases up to \(e\) and then increases, and \(\sqrt m\ge4\). Summing over these primes and using \(\sum_{p\mid m} v_p(m)\log p=\log m\) bounds their total contribution by \(2/\sqrt m\).

There is at most one prime divisor \(p>\sqrt m\). If \(m=sp\) with such a \(p\), then \(s<p\), \(v_p(m)=1\), and \(v_p((m-1)!)=s-1\). Its contribution is exactly \(a_s\). Conversely any representation counted by \(W_Q\) has \(s\le\sqrt n<\sqrt m\) and hence \(p>\sqrt m\). An omitted large prime contributes at most \(a_{Q+1}\). Summing over the \(h\) steps proves (1). The one-step approximation in terms of the largest prime factor is classical. [Erdős, Graham, Ivić and Pomerance, Theorem 2](https://math.dartmouth.edu/~carlp/factorial.pdf)

Consequently, at any **fixed** \(C>0\), with \(h=h_C(n)\), all-start divergence of \(G(n,h)\) is equivalent to
\[
\sum_{s\le h}\frac{\pi((n+h)/s)-\pi(n/s)}{s}\longrightarrow\infty
\qquad(n\to\infty).
\tag{2}
\]
Indeed, (1) at \(Q=h\) gives a remainder of at most \(1+2h/\sqrt n\), and concavity of the logarithm gives \((\log 2)/s\le a_s\le 1/s\). Taking \(Q=\lceil h\log(2h)\rceil\) in (1) gives an additive error tending to zero for the logarithmically weighted sum \(W_Q\).

## 2. A single prime multiple at each start

Consider the following assertion, denoted by **H1**. For some fixed integer \(A\ge1\) and every sufficiently large integer \(x\), there exist an integer \(1\le s\le h_A(x)\) and a prime \(p\) with
\[
x<sp\le x+h_A(x).
\]

**Proposition.** Part (i) holds if and only if H1 holds. If H1 holds with exponent \(A\), every fixed \(C>2A\) gives \(G(n,h_C(n))\gg_{A,C}(\log n)^{C-2A}\). Conversely, if part (i) holds at exponent \(C\), a hit occurs with both bounds equal to \(h_C(x)\) for every sufficiently large \(x\).

For the converse, (2) implies that its sum has a positive term for each sufficiently large start. Enlarging \(C\) to an integer if necessary gives H1. For the forward direction, let \(b=\lfloor(2\log n)^A\rfloor\), \(h=h_C(n)\), and partition the first \(b\lfloor h/b\rfloor\) integers after \(n\) into consecutive blocks of length \(b\). Each block starts at an integer \(x\) in \([n,2n]\) for large \(n\), so \(h_A(x)\le b\). By H1 the block contains a hit \(sp\) with \(s\le b\). Since \(b^2<n\), its contribution to the log gain is at least \(\log(1+1/b)\ge1/(2b)\). These disjoint blocks give a total at least \(\lfloor h/b\rfloor/(2b)\), as claimed.

## 3. The endpoint \(C=2.1\) at almost every integer start

**Theorem.** There are absolute constants \(c_0,\eta>0\) such that, for all sufficiently large \(X\),
\[
\#\{3\le n\le X:\ G(n,h_{2.1}(n))<c_0(\log n)^{1/20000}\}
\ll X/(\log X)^\eta. \tag{3}
\]

Set \(L=\log X\), \(c=2.1\), \(H=L^c\), \(b_1=c-1-1/10000\), and \(b_2=c-1-1/20000\). Matomäki and Teräväinen prove estimates for their prime minorant \(\rho^-\) in the band \(L^{b_1}<q\le L^{b_2}\), where \(q\) is prime. Let \(A_u(x)\) be \(u^{-1}\) times the sum of \(\rho^-(r)\) over \(x<qr\le x+u\) in this band. Their equations (2.7) and (2.8) give, for absolute \(\gamma,\varepsilon>0\) and \(H_1=X^{99/100}\),
\[
A_{H_1}(x)\ge \gamma/L\quad(X<x\le2X),\qquad
\int_X^{2X}|A_H(x)-A_{H_1}(x)|^2\,dx\ll X/L^{2+\varepsilon/2}.
\]
Thus \(A_H(x)\ge\gamma/(2L)\) except on a set of real \(x\) of measure \(O(X/L^{\varepsilon/2})\). Here \(2\sqrt X\le r\le3X\) for large \(X\), so their Theorem 2.1(i) allows us to replace \(\rho^-(r)\) by the prime indicator as a lower bound for the resulting prime count. There are therefore at least \(\gamma H/(2L)\) products \(qr\) of two primes in \((x,x+H]\) at each good real start. Each product occurs once because \(q\le L^{b_2}<r\) and \(r>L^{b_2}\). [Matomäki and Teräväinen, *Almost primes in almost all short intervals II*, Theorem 2.1 and equations (2.7)–(2.8)](https://arxiv.org/pdf/2207.05038#page=5)

To pass to integer starts, use the disjoint unit intervals \([n,n+1)\subseteq[X,2X]\). All but \(O(X/L^{\varepsilon/2})\) contain a good real \(x\). For such a choice, every counted product is greater than \(n\) and at most \(n+1+H\). At most one integer exceeds \(n+\lfloor H\rfloor\) in that range. Discarding it leaves \(\gg L^{c-1}\) distinct hits in \((n,n+h_c(n)]\), since \(\log n\ge L\). Each contributes at least \(\log(1+1/q)\ge1/(2L^{b_2})\) to the factorial log gain. The resulting exponent is \(c-1-b_2=1/20000\). On \([X,2X]\) the logarithms of \(n\) and \(X\) are comparable. Summing dyadic bounds down to \(\sqrt X\) and counting smaller starts trivially proves (3), with \(\eta=\varepsilon/2\) for a fixed admissible \(\varepsilon\).

The narrow band in the proof of Matomäki and Teräväinen's Theorem 1.1 supplies the positive exponent. The endpoint \(q\le L^{1.1}\) in their headline statement alone would yield a constant lower bound by this calculation.

## Hand checks

At \(n=20,h=3,Q=2\), the sum records \(22=2\cdot11\) and \(23=1\cdot23\), so \(W_2=\log3\). Direct factorization at the three steps gives \(D(23)/D(20)=(4/3)(10/9)(3/2)(20/19)\cdot2=800/171\), in agreement with (1). In the density argument, the exponent saving uses the upper end of the narrow band, each semiprime contributes at its own integer step, and the passage through a unit interval costs at most one of the counted steps. The exceptional-set estimate in (3) still permits infinitely many exceptional integers.
