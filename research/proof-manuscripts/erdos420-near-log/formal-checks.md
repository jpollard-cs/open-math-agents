# Lean verification of the factorial-window construction

Jordan Pollard · November 27, 2026  
OpenAI Codex developed the arguments and the Lean files.

The finite averaging argument uses no imports beyond Lean core. The proof in `SeedAverage.lean` gives a union bound for a finite list of divisibility obstructions and finds a seed in the prescribed interval. The budget counts the exact positive multiples of each listed modulus.

`TranslatedDivisorCover.lean` combines simultaneous hits at exceptional offsets with divisors at the other offsets. Its second lemma proves that a divisor strictly between the cofactor cutoff and the square root excludes every prime multiple with cofactor at most that cutoff. Both this file and the averaging lemma compile with Lean 4.33.1. In the original prime-gap project, using Lean 4.33.0, `LcmSeed.lean` shows that every positive integer failing to divide the LCM has a prime-power divisor above its cutoff. It supplies the exceptional set in precisely the format required by the root theorem.

The paper's simultaneous-residue theorem comes from [OpenAI's prime-gap formalization at commit 03a1190](https://github.com/openai/LongGapsBetweenPrimes/tree/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b), which pins Lean 4.33.0. The module `PrimeGapTranslatedCover.lean` applies that theorem to the actual LCM progression. The module `FactorialGain.lean` checks the estimate in the next paragraph from the definition of the divisor count. The asymptotic size of the exceptional set and the choice of window parameters are proved in the manuscripts.

The combined theorem compiled in Lean 4.33.0 using the original upstream module at the pinned revision. For the integrated theorem, set $z=2w+h+1$ and let $Q$ consist of the prime powers $q$ with $N<q\le z$. Its numerical hypothesis is
$$
h\sum_{q\in Q}\left\lfloor\frac zq\right\rfloor\le(w+1)r,
\qquad r\le\delta x .
$$
With the stated size inequalities for the sieve primes and the search interval, the theorem produces a translate and proves the log divisor gain there is at most $2h/w$. The continuous parameter $x$ is the input to the upstream sieve. The integer $N$ is the cutoff used in the least common multiple. The asymptotic application takes $N=x$ at integer $x$. [Combined theorem](CertifiedFactorialWindow.lean) · [Reproduce the checks](check-lean.sh)

A short argument connects a divisor certificate to a factorial window. Let $S(m)$ be the sum of the prime factors of $m$ with multiplicity. Then $S(de)=S(d)+S(e)$ and $S(m)\le m$. For the inequality, multiplying two factors $u,v\ge2$ only increases their size relative to adding them, since $uv\ge u+v$. At a factorial step $m$, the contribution from a prime $p$ to the log divisor ratio is at most $p\,v_p(m)/m$ by Legendre's formula and $\log(1+y)\le y$. [Freiberg, Lemma 4.1](https://arxiv.org/abs/2609.15597) Thus if $m=de$ and both factors exceed $w$, the log gain is at most $S(m)/m\le1/d+1/e\le2/w$. Summing over a window of $h$ certified positions gives the finite bound $2h/w$.

The known target requiring a delay of $c\log n$ for each fixed $c$ has a simpler remaining counting problem. One may take $h$ and $w$ to be fixed multiples of the sieve parameter $x$, with $w>4h$. Then $z=2w+h+1=O_c(x)$ and each obstructing prime power $q>x$ contributes at most $z/q=O_c(1)$ multiples. The density-zero estimate for prime powers makes their total contribution $o_c(x)$. The full iterated-logarithm bound needs control of the sum of these reciprocals with a growing ratio $z/x$.
