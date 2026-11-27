# Limit points of short products of consecutive factorial-divisor ratios

This AI-authored manuscript by Codex, written at Jordan Pollard's request, presents a full written proof for the original density questions in Erdős #420(ii) and (iii). It is posted for external review. Priority and independent human verification are pending.

For every growing real window length f(n)=O(log n), the finite limit points of the factorial divisor-count ratio are exactly [1,∞). For any prescribed integers D≥1 and r≥0, the proof constructs arbitrarily large starting integers such that the ratios approach (1+1/D)^r simultaneously over every integer window length from a fixed threshold to C log n. It permits nonmonotone f. The final section extends the range to every growing f=o(log n · log₂ n · log₄ n/(log₃ n)³) and gives a count of the witnesses.

- [Read the five-page manuscript](factorial-density.pdf) or [its TeX source](factorial-density.tex).
- [Independent AI derivation and hypothesis audit](independent-audit.md).
- [Finite arithmetic checker](check_structure.py) and [output](structure-tests.txt). Run with Python 3.
- [Lean proof of the discrete suffix-count lemma](SuffixCount.lean) and [its axiom audit](suffix-audit.txt).

The general analytic argument uses the published EGIP one-step estimate, the Banks–Freiberg–Maynard theorem on distribution in progressions, Maynard’s rough prime clusters, and the arithmetic large sieve. The general proof is written. The Lean file proves only the discrete selection lemma.

Part (i), which asks for divergence for all sufficiently large starting integers in sufficiently large logarithmic powers, remains open. The separately submitted [four-ninths formalization](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8125) concerns a known larger window.

For reproducibility the bibliography gives the exact external statements, including the simultaneous roughness conclusion in the proof of Maynard's Theorem 3.1. The argument bounds total unwanted mass at the same starts at which the prime cluster occurs. A CRT guard by itself, or an unconditioned estimate on typical starts, would leave this step open.
