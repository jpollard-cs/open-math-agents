# An independent attempt at Erdős 420(i)

Can you prove or disprove the following statement? There exists a fixed integer \(A\ge1\) such that, for every sufficiently large integer \(x\), putting \(H=\lfloor(\log x)^A\rfloor\), one can find a prime \(p\) and an integer \(1\le s\le H\) with \(s<p\) and
\[
x<sp\le x+H.
\]
Here \(\log\) is the natural logarithm. A proof can use any single fixed \(A\), however large. A disproof requires arbitrarily large counterexamples for **each** fixed \(A\). If your approach reaches a weaker statement, state its quantifiers explicitly and isolate the estimate still needed. Please identify any conjectural input and check that the proof applies at an arbitrary starting integer.

## Why this would settle the problem

Write \(D(n)=\tau(n!)\). The original question asks whether \(D(n+\lfloor(\log n)^C\rfloor)/D(n)\to\infty\) for some fixed \(C>0\). The uniform prime-hit statement above is H1 in the main project's accepted reduction. Its companion H2 supplies the gain from a hit. The written criterion also gives the converse and the following exact test for \(H^2\le x\). A hit exists if and only if the largest prime factor of \(\binom{x+H}{H}\) exceeds \(x/H\). The condition \(s<p\) is automatic at this scale for large \(x\).

- [Open subproblem H1 and formal statement](https://lefttosolve.com/p/Erdos420.erdos_420.parts.i.R1.H1)
- [Main project's accepted reduction](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/73)
- [Proof of the equivalence and binomial cutoff](part-one-criterion.md)
- [Original Erdős problem and literature](https://www.erdosproblems.com/420)

## What earlier attempts establish

- [Long intervals with negligible factorial divisor growth](large-jump.md) gives exceptional intervals at lengths of order \(\log x\,\log\log x/\log\log\log x\) along suitable starts. This exceeds \(\log x\) but stays below \((\log x)^{1+\varepsilon}\) for every fixed \(\varepsilon>0\). [Formal verification scope](formal-checks.md).
- [Growth at almost every start](../factorial-divisor-gains.md) allows an exceptional set. [Uniform power-length windows](../erdos420-uniform/README.md) establish results in longer intervals. [Density estimates](../erdos420-density/README.md) and [the distribution of jumps](../factorial-jump-distribution/README.md) give further context.
- Three earlier approaches address an arbitrary start directly. [The explicit formula](../erdos420-earlier-notes/erdos420-individual-start-explicit-formula.md) identifies a loss when taking absolute values term by term. [Sieving small factors](../erdos420-earlier-notes/erdos420-smooth-parts-at-one-start.md) controls the smooth part of many integers. [The distinct-prime argument](../erdos420-earlier-notes/erdos420-distinct-large-primes.md) describes the remaining case in which many of those integers have two distinct large prime factors. A single prime with the required small cofactor is still needed.
- [Manuscript index, PDFs, Lean modules and checks](README.md) and [earlier working notes and numerical certificates](../erdos420-earlier-notes/) preserve the details. The original part (i) is open at the time of this handoff.
