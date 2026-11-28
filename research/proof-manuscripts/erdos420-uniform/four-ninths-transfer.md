# How a shorter factorial window strengthens the four-ninths bound

*Jordan Pollard, November 27, 2026. OpenAI Codex derived the argument and prepared the Lean files.*

Write $D(n)=\tau(n!)$, put $c=2177/5000=0.4354$, $\delta=1/100000$, and $b=1-c+\delta$. Our shorter-window manuscript proves that every sufficiently large real $x$ has $\gg x^c$ distinct primes greater than $x^b$ dividing an integer in $(x,x+x^c]$. In particular it gives $\log(D(n+\lfloor n^c\rfloor)/D(n))\gg n^\delta$ uniformly in the start $n$. The following deductions use that written analytic estimate. [Shorter-window manuscript and numerical certificates](https://github.com/jpollard-cs/open-math-agents/tree/671d7a4fb18e8e49d5b17df5d748cf425ef4ef8b/research/proof-manuscripts/erdos420-uniform)

## Amplifying the gain

For every sufficiently large $n$ and every integer $H$ with $\lfloor n^c\rfloor\le H\le n$,
$$
 \log\frac{D(n+H)}{D(n)}\gg H n^{\delta-c}.
$$
Consequently, for $H=\lfloor n^{4/9}\rfloor$ the logarithm of the ratio is $\gg n^{8149/900000}$, since $4/9-c+\delta=8149/900000$. The ratio itself is at least $\exp(Cn^{8149/900000})$ for some $C>0$ and all sufficiently large $n$. This exceeds the doubling required by the four-ninths variant. The polylogarithmic window in Erdős #420(i) remains open. [Formal conjecture](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/ErdosProblems/%C2%AB420%C2%BB/)

**Proof.** Set $L=\lceil(2n)^c\rceil$. If $H\ge L$, divide $(n,n+H]$ into $\lfloor H/L\rfloor$ consecutive blocks of length $L$ and a remainder. A block starting at $x$ contains the whole window $(x,x+\lfloor x^c\rfloor]$, since $x\le2n$. Its logarithmic gain is $\gg x^\delta\ge n^\delta$ by monotonicity of $D$. Adding the gains telescopes. The number of blocks is at least $H/(2L)$, and $L\ll n^c$. If $H<L$, the window at $n$ already gives $\gg n^\delta$, which suffices since $H\ll n^c$. All implied constants are independent of $H$.

## The open intermediate-prime estimate

Take $h=\lfloor n^{4/9}\rfloor$, $A=n^{4/9}$, $B=n^{5/9+1/10000}$. The open step in the project's original reduction asks whether the primes in $(A,B]$ contribute at most $(5/9-\eta)h\log n$ for some fixed $\eta>0$, counting prime factors of $n+1,\ldots,n+h$ with multiplicity.

The shorter-window prime count implies that $\gg h$ positions in $(n,n+h]$ carry a prime greater than $B$. Indeed, apply the same block partition. Distinct primes greater than $x^b$ in one short window divide distinct integers there, because $(x^b)^2>x+x^c$ for large $x$. Also $x^b\ge n^b>B$, since $b-(5/9+1/10000)=8059/900000$. The positions in different blocks are disjoint. Also $B>h$, so no qualifying prime can divide two different window terms. This gives $\gg h$ distinct large primes in the full window. Each contributes at least $\log B$, so the large primes together contribute at least $\rho h\log n$ for some $\rho>0$. Alternatively the classical large-prime count gives this conclusion directly at $4/9$. [Erdős, Graham, Ivić and Pomerance, Lemma 3](https://math.dartmouth.edu/~carlp/factorial.pdf)

For each prime $p>h$ the valuation of $\binom{n+h}{h}$ equals $\sum_{i=1}^h v_p(n+i)$, since $v_p(h!)=0$. All intermediate and large primes are greater than $h$. Their combined logarithmic contribution is therefore at most $\log\binom{n+h}{h}$. Furthermore
$$
 \log\binom{n+h}{h}\le h(\log(n+h)-\log h+1)=(5/9+o(1))h\log n .
$$
The inequality follows from $\binom{n+h}{h}\le(n+h)^h/h!$ and $\log(h!)\ge h\log h-h$. Subtract the large-prime contribution to obtain the intermediate-prime estimate with $\eta=\rho/2$ for all sufficiently large $n$.

The Lean file WindowTiling.lean verifies the finite counting argument for any nondecreasing cumulative count and any admissible variable short-window lengths. The analytic short-window theorem is an input to the deductions above. Completing the project’s proof requires a Lean proof of the large-prime counting estimate.
