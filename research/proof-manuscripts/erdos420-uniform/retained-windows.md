# Divisor growth after deleting factors in a four-ninths window

Codex (AI), at Jordan Pollard's request, November 27, 2026. This is a consequence of the large-prime estimates of Erdős, Graham, Ivić and Pomerance (EGIP). The quantitative input used here is the 48-band formalization in this directory. Priority for the deletion formulation has not been established.

Let δ=1/10000, η=1/5000, h=⌊n^(4/9)⌋ and B=n^(5/9+δ). For any set of omitted indices E⊂{1,…,h}, write

$$Q_E(n)=\frac{\tau\left(n!\prod_{1\le i\le h,\ i\notin E}(n+i)\right)}{\tau(n!)}.$$

The indices may be chosen after the complete prime factorizations of the interval are known. For every fixed real α∈[0,1],

$$\liminf_{n\to\infty}\ \min_{|E|\le\alpha h}\frac{\log Q_E(n)}{n^\delta}
\ \ge\ \max(\eta-\alpha,0).$$

In particular, deleting up to one factor in ten thousand still leaves at least exp(c n^δ) divisor growth for every fixed c<1/10000 and every sufficiently large n. The original four-ninths result is the doubling corollary of EGIP. The original conjecture on polylogarithmic windows remains open.

## Counting rows before deleting them

For a row n+i, split its logarithm according to the prime factorization, with log p counted once per copy of p. The checked small-prime theorem gives total mass at p≤n^(4/9) at most (4/9+ε)h log n for any ε>0 and all sufficiently large n. The checked theorem `FactorialGrowth.mesh_saving FactorialFullBands.all_bands` gives total mass at n^(4/9)<p≤B at most (5/9−η)h log n. The mass of all rows is at least h log n, so the mass above B is at least (η−ε)h log n. A row can supply at most log(n+h). Consequently the number J of rows with a prime factor above B satisfies

$$J\ge (\eta-\epsilon)h\frac{\log n}{\log(n+h)}.$$

This holds simultaneously for every choice of E. At least max(0,J−|E|) surviving rows still have a prime factor above B.

## Keeping the multiplicative gains

Choose one such prime from each surviving row. They are distinct because B>h and no prime larger than h can divide two integers in an interval of h consecutive integers. Eventually B²>n. For a chosen p, its exponent in n! is ⌊n/p⌋. Multiplying by the retained window raises this exponent by at least one, giving a divisor-count factor at least

$$1+\frac1{1+\lfloor n/p\rfloor}\ \ge\ 1+\frac{B}{n+B}.$$

All other prime factors contribute a ratio at least one. The logarithm of the right-hand side is asymptotic to B/n, and hB/n is asymptotic to n^δ. Combining with the count, taking a liminf and letting ε decrease to zero proves the statement. The quantifiers allow the worst deleted set to vary with n.

## A finite version and exact arithmetic checks

At an arbitrary n≥1 let h≤n, choose 0≤B≤n and let G be the offsets with a prime factor above B. One has the finite estimate

$$\log Q_E(n)\ \ge\ \frac{|G\setminus E| B}{16n}.$$

One argument compares ordinary factorial steps to the steps after deletion. For positive a,b,c with a dividing b,
τ(bc)τ(a)≤τ(ac)τ(b). Prime by prime, writing u≤v for the exponents in a,b and k for that in c, the difference after cross multiplication is k(v−u)≥0. Every retained prefix divides the full factorial prefix, so the multiplicative gain of the retained step is at least the usual gain. At a surviving good offset the project's one-step estimate gives at least 1+B/(8n). Use log(1+x)≥x/2 for 0≤x≤1, then add over all surviving good offsets.

`check_thinning.py` checks 46,656 instances of the divisor inequality and 96,232 finite window estimates using integer arithmetic. In fact the latter check the product bound (1+B/(8n))^|G\\E| itself. These checks supplement the arguments for arbitrary n. The liminf statement above is a written result. Three supporting results have been checked locally in Lean 4.33.1. The undeleted ratio is eventually at least exp(n^δ/640000). After deleting any set of at most h/40000 offsets, it is eventually at least exp(n^δ/1280000). The divisor comparison for a dividing b is also formalized. See [the undeleted proof](ExponentialFourNinths.lean), [the deletion proof](RobustFactorialGrowth.lean), [the divisor comparison](DivisorDiminishingReturns.lean), and [the axiom audits](retained-lean-audits.txt).

Sources: [EGIP, Lemma 3 and Corollary 3](https://math.dartmouth.edu/~carlp/factorial.pdf), [submitted four-ninths mass proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8125), and the local modules `ReciprocalGrowthBands.lean`, `ReciprocalAllBands.lean` and `ReciprocalOfficialSmallPrimes.lean`.

The count gives a positive fraction of good offsets across the full window. It permits concentration at one end and therefore supplies no uniform bound in a polylogarithmic prefix.
