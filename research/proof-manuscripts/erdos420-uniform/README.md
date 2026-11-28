# Uniform factorial-divisor growth

The note proves an unconditional individual-start bound

\[
\log\frac{\tau((n+\lfloor n^{0.4354}\rfloor)!)}{\tau(n!)}
\gg n^{1/100000}
\]

for every sufficiently large integer `n`.  This improves the exponent `4/9`
in Erdős–Graham–Ivić–Pomerance (1996), but does **not** solve the
polylogarithmic window asked for in Erdős #420(i).

Reproduce the two independent exact numerical certificates with:

```sh
python verify_bilinear.py
python check_five_terms.py
```

The first certificate composes the established exponent-pair range with the
Baker–Harman trilinear ranges.  The second clips all five published monomial
terms directly on a different rational mesh.  Both use exact rational
arithmetic.  The general analytic proof is written in the note; the scripts
certify its finite inequalities, not the analytic lemmas themselves.

Codex and collaborating AI agents produced the argument and writing at the
account owner's request.  Priority and external mathematical review are
unconfirmed.

