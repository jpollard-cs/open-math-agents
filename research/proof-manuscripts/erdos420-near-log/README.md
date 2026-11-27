# Erdős 420 and the divisor count of a factorial

The [main proof (PDF)](large-jump.pdf) constructs long windows in which the ratio of factorial divisor counts tends to one. Write $D(n)=\tau(n!)$. For fixed $B>0$ and $0<\rho<1$, every interval $[X,X+Y]$ with $X\ge Y$ and $Y$ sufficiently large contains at least $Y^{1-\rho}$ starting integers $n$ such that
$$
\log\frac{D(n+H)}{D(n)}\ll_B(\log_2Y)^{-B},
\qquad H=\left\lfloor c_{B,\rho}\frac{(\log Y)(\log_2Y)}{\log_3Y}\right\rfloor .
$$
Here $\log_j$ denotes the $j$-fold iterated natural logarithm. The proof also bounds the length attainable by a fixed congruence class followed by repairs at individual offsets. The window length improves the order of Theorem 1.1 in [Tristan Freiberg's September 2026 preprint](https://arxiv.org/abs/2609.15597). The proof uses an existing [Lean theorem about simultaneous residues](https://github.com/openai/LongGapsBetweenPrimes/blob/03a1190d0bc5502d9f54eeb60ad3e45e22b0df0b/LongGapsBetweenPrimes.lean#L3480-L3486). The asymptotic deduction for factorials is a written proof. Two finite steps were checked on Lean 4.33.1. [Lean source](TranslatedDivisorCover.lean) · [Compiler transcript](translated-divisor-lean-check.txt) Erdős 420(i) asks for uniform growth for some fixed power of the logarithm and remains open.

| Manuscript | Contents |
| --- | --- |
| [Long intervals with negligible factorial divisor growth](large-jump.pdf) · [source](large-jump.md) | The main bound, translated multiplicity, and the limit of this congruence construction |
| [The full logarithmic window](logarithmic-window.pdf) · [source](logarithmic-window.md) | For the exact window $\lfloor\log n\rfloor$, the ratio approaches one with a power saving in $\log n$. The argument quantifies the tradeoff as the window grows. |
| [A largest-prime-factor criterion](part-one-criterion.pdf) · [source](part-one-criterion.md) | A prior equivalent formulation of part (i) and its consequence for the largest prime factor of a binomial coefficient on these intervals |
| [Frequency of doubling in short windows](critical-law.pdf) · [source](critical-law.md) | An unconditional error estimate below the logarithmic scale, and a limiting law at the logarithmic scale conditional on a uniform prime-tuples conjecture |
| [Small gains at many starts](flat-windows.pdf) · [source](flat-windows.md) | A covering argument giving sharper decay at shorter windows |
| [Constants at the Rankin scale](freiberg-constant.pdf) · [source](freiberg-constant.md) | A separate refinement providing $Y^{1-o(1)}$ starts at a fixed multiple of Freiberg's window length |

Jordan Pollard is the named author. OpenAI Codex developed and checked the arguments and prepared the manuscripts. The Python scripts check finite arithmetic identities and examples. Run each with Python 3.9 or newer.

```sh
python3 check-large-jump.py
python3 check-cover.py
python3 check-critical.py
```
