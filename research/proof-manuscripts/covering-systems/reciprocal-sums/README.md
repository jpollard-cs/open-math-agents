# Irreducible covers at every cardinality

The manuscript proves a reciprocal-sum lower bound at every sufficiently large cardinality and gives the sharp asymptotic, through an additive term tending to zero, among zero-defect covers. It also reports exact finite values of the unrestricted minimum largest modulus. The mathematical claims have a written proof and await independent review.

## Relation to the catalog target

For distinct moduli in increasing order, the i-th modulus is at least i + 1. Hence every reciprocal sum is at most H_(k+1) − 1. Together with the manuscript's all-size lower bound, this gives R(k) = Θ(log k), the order-of-growth formulation of part (iii). Earlier work reports that order. The sharper claim for review is the coefficient 1/2 at every sufficiently large size, the question in Remark 6.5 of Ege Öztürk's preprint, and the additive asymptotic in the zero-defect class. This is an AI-authored written submission for review. The unrestricted leading coefficient remains unknown here.

## Reproduce the computations

The Python programs use only the standard library. Run them in a writable directory with Python 3.10 or later.

- Run `python reciprocal.py 100 1000 10000 100000` to generate covers and check their size, digit structure, terminal least common multiple, and defect. The printed columns give the requested size, largest modulus, reciprocal sum and reciprocal sum divided by the natural log of the size. Import `make(k)` to obtain the actual list of (modulus, residue) pairs.
- Run `python enumerate_covers.py 47` for the enumeration by prime-power contraction. The output file `covers-through-47.json` lists every qualifying set of moduli in increasing cardinality order.
- Run `python exact_minima.py` for the independent cap-36 calculation. It checks every candidate subset and writes `bounded-covers.json`, containing one residue assignment for each of the 29 irreducible sets. Each listed assignment is checked at all 360 residues.
- Run `python crosscheck.py` to compare the complete bounded lists, validate the tabulated extrema, and verify the constructor at every size from 5 through 1000.

The modulus cap and the cardinality are different bounds. The list through cap 47 is exhaustive for sets with largest modulus at most 47. For each cardinality represented in that list, its smallest listed maximum is also the unrestricted minimum at that cardinality. All general estimates in the manuscript are mathematical arguments; numerical sum columns are rounded and illustrative.

The PDF is accompanied by editable LaTeX source. A standard TeX Live installation with pdfLaTeX and the packages listed in the preamble can compile it.

The [defect-dependent upper bound](./defect-tradeoff.md) quantifies the extra classes required for an unrestricted gain above the one-half coefficient. Run `python check_defect.py` for the rational finite checks.

The [finite extension](./finite-extension.md) gives the exact unrestricted minima through 23 classes, including eight new cardinalities. Its witness file contains actual residues for each new entry.

The [cap-60 enumeration](./finite-60.md) proves $m(24)=m(25)=60$, with covering residues and one-modulus deletion checks. The [grouped-digit note](./grouped-digits.md) gives sharp reciprocal sums and the asymptotic minimum largest modulus for the class it describes, plus necessary conditions for improving either bound without a structural restriction.
