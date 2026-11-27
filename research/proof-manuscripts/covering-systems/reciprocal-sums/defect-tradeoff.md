# How many extra moduli are needed to gain reciprocal mass?

Codex, at the request of Jordan Pollard · 27 November 2026 · written addendum for review

Let A be an irreducible set of k distinct covering moduli greater than one. Write M = max A, L = lcm A, and δ = k − 1 − b(L), where b(L) = ∑ v_p(L)(p−1). The reciprocal sum is S(A) = ∑ 1/n over n ∈ A. The matching lemma on page 2 of the [companion proof](./erdos1189-reciprocal-sums-and-exact-minima.pdf) gives the following bound for **every** such set as k grows, with an absolute implicit constant.

$$
S(A) \le \tfrac12\log k + (1-\log 2)\log(1+\delta)
                 + O(\log\log(k+3)).
$$

For fixed ε > 0, attaining at least (1/2 + ε) log k therefore requires δ ≥ k^{ε/(1−log 2)−o(1)}. For example, a sequence attaining coefficient 3/4 requires δ ≥ k^{0.8147…−o(1)}. A sequence attaining Öztürk’s upper coefficient 3/2 − log 2 would require δ = k^{1−o(1)}. A subpolynomial defect forces an upper coefficient of 1/2. The zero-defect construction attains that coefficient at every sufficiently large exact size. Whether any positive fixed gain above 1/2 can be attained remains open in this work.

## A finite inequality

Let P(n) be the largest prime factor of n ≥ 2, let H_m be the m-th harmonic number, and put

$$
I(L)=\{p^j d : p\mid L,\ 1\le j\le v_p(L),\ 1\le d<p\},\qquad
U(L)=\sum_{p\mid L}\sum_{j=1}^{v_p(L)}\frac{H_{p-1}}{p^j}.
$$

The representations in I(L) are unique: p is the largest prime factor, j is its exact exponent, and d is the remaining factor. Thus U(L) is the reciprocal sum of I(L). Some members of I(L) need not divide L, which only strengthens the subtraction below.

For every real y ≥ 1,

$$
 S(A)\le\frac1M+U(L)+\frac{\delta}{y}
   +\sum_{\substack{2\le n\le y,\;n\mid L\\ n\notin I(L)}}
              \left(\frac1n-\frac1y\right).
\tag{1}
$$

To see this, remove the largest modulus and match the b(L) slots to distinct remaining moduli. A slot for (p,j) must receive a multiple of p^j. There are δ unmatched moduli. Split the weight into w(n) = min(1/n,1/y) and g(n) = (1/n−1/y)_+. Each unmatched entry contributes at most 1/y to the w-sum. Since w decreases, the w-sum for the p−1 matched multiples in a row is at most the w-sum at p^j, 2p^j, …, (p−1)p^j. Across all rows this gives ∑_{I(L)} w = U(L) − ∑_{I(L)} g. The g-sum over the actual moduli under consideration is at most ∑_{n|L, n≥2} g(n). Cancel the common terms. Dropping any remaining negative terms proves (1).

If n | L and P(n) > √n then n = P(n)d with d < P(n), so n ∈ I(L). More generally the exact exception among divisors is d ≥ p when n = p^j d with p = P(n). The last sum in (1) is therefore bounded above by the same sum over all 2 ≤ n ≤ y satisfying P(n) ≤ √n.

There is a convenient discrete form. Order the divisors n ≥ 2 of L outside I(L) as e₁ < e₂ < ⋯ < e_h. Optimizing the threshold in (1) gives

$$
 S(A) \le 1/M+U(L)+\sum_{r=1}^{\min(\delta,h)}1/e_r.
$$

For 1 ≤ δ ≤ h take y = e_δ, so the constant subtractions cancel δ/y. For δ = 0 use y = 1, and for δ > h send y to infinity. Even without knowing L, the first possible exception is 12: each integer from 2 to 11 has remaining cofactor smaller than its largest prime after all copies of that prime have been removed. Thus at defect one the extra term is at most 1/12.

## Estimating the exception

The number of integers 2 ≤ n ≤ x with P(n) > √n equals

$$
 \sum_{p\le\sqrt x}(p-1)+\sum_{\sqrt x<p\le x}\lfloor x/p\rfloor .
$$

Indeed they are precisely the products pd ≤ x with d < p, each counted once. The first sum is O(x/log x), and replacing floors in the second costs O(x/log x). The classical prime reciprocal estimate on (√x,x] is log 2 + O(1/log x). Thus, writing D(x) for the number of exceptions P(n) ≤ √n, one obtains D(x) = (1−log 2)x + O(x/log x). Integration gives

$$
 \sum_{\substack{2\le n\le y\\P(n)\le\sqrt n}}
       (1/n-1/y)=\int_1^y D(t)t^{-2}\,dt
       =(1-\log 2)\log y + O(1+\log\log(y+3)).
$$

Finally take y = 1+δ in (1). The prime-budget estimate on pages 2 and 4 of the companion proof gives U(L) ≤ (1/2)log k + O(log log(k+3)) for arbitrary defect, because b(L) ≤ k−1. This proves the claimed uniform bound. Taking δ ≤ k−1 recovers the unrestricted upper coefficient in [Ege Öztürk, Theorem 1.4](https://www.researchgate.net/publication/413884122). The defect-dependent interpolation is the point of this addendum. Historical priority and independent proof review are pending.

## Exact finite check

Run `python check_defect.py` in this directory. It checks (1) by rational arithmetic at every integer threshold y from 1 to M+1 on all 741 irreducible sets enumerated with M ≤ 47. This validates finite instances; the argument above covers arbitrary periods and real thresholds.
