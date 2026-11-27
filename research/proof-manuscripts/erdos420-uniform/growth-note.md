# Growth of the divisor count in the four-ninths window

Jordan Pollard, with OpenAI Codex assistance, November 27, 2026.

Write $h=\lfloor n^{4/9}\rfloor$. Keeping the dependence on $n$ in the original four-ninths argument yields, for all sufficiently large integers $n$,

$$
\frac{\tau((n+h)!)}{\tau(n!)}\ge 1+\frac{n^{1/10000}}{320000}.
$$

In particular this ratio tends to infinity, which implies the project's eventual factor of two. This growth bound is a consequence of the 1996 argument of Erdős, Graham, Ivić and Pomerance. The same limit in a window of length $\lfloor(\log n)^C\rfloor$ remains open.

To see where the exponent comes from, write $A=n^{4/9}$ and $B=n^{5/9+1/10000}$. A fixed saving $\eta$ in the logarithmic contribution from the intermediate primes, together with the small-prime estimate, yields at least $\eta A/8$ window positions with a prime factor above $B$. Each such position increases the divisor count by at least $B/(8n)$ times its value at the start of the window. Summing and using $AB/n=n^{1/10000}$ gives the coefficient $\eta/64$. The 48-band proof supplies $\eta=1/5000$.

The accepted small-prime proof is by OrangeHeadz. The large-prime count and gain estimates are in steveDOTdigital's parent reduction. The new intermediate-prime proof submitted in PR #8125 supplies the other input. [Original paper, Lemma 3 and Corollary 3](https://math.dartmouth.edu/~carlp/factorial.pdf) · [Parent reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5169) · [Small-prime proof](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5473) · [Intermediate-prime submission](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8125).

Run `lake env python3 /path/to/verify-reciprocal-bands.py ReciprocalGrowthApplied` in the pinned formal-conjectures checkout with the Mathlib cache. The two final declarations are `FactorialGrowth.four_ninths_growth` and `FactorialGrowth.four_ninths_tendsto`.
