# Optimal periods, prime squares, and exact minima at 26 and 27 moduli

Codex (OpenAI), at Jordan Pollard’s request. Public research manuscript for review, 27 November 2026.

[Read the paper](period.pdf). Its first two sections evaluate the arithmetic divisor maximum in Section 8 of Ege Öztürk’s preprint, through its constant term. For the explicit smooth-number envelope they also determine the first term of the vanishing difference and the optimal prime-square threshold. Coverage alone eventually costs zero in the arithmetic problem. The paper links the additive cost of irreducibility to the largest modulus. The leading unrestricted upper coefficient belongs to Öztürk. The companion thread supplied the ten minima through cardinality 25 and the stronger error in the defect interpolation.

For the relaxed period problems the largest prime raised to power $j$ has different sharp thresholds for maximizing reciprocal mass and minimizing the largest selected divisor. Section 2 proves both thresholds for every fixed $j$, along with the sharp cost of the cutoff in either calculation. The two arithmetic objectives eventually require different periods.

At size 26 the minimum largest modulus is 70. The finite search finds exactly one extremal modulus set. Two decision procedures check the positive example and the impossibility of a cover after every deletion with all residues freely reassigned. The residue assignment also has a stand-alone Lean check for every integer. At size 27 the minimum is 72, with exactly three extremal sets. Size 28 requires at least 84. The unrestricted sharp reciprocal coefficient and the general minimum largest modulus remain open.

## Reproduce the checks

Use Python 3.10 or later in this directory. The finite searches use the standard library. The two cap-70 solvers can take several minutes.

```sh
python check_period.py
python fixed_sizes.py
python crosscheck.py
python cap60.py
python verify60.py
python cap70.py > cap70-checks.txt
python mixed70.py
python witness70.py
python second70.py example26.json
lean Size26.lean
```

The first two decision procedures project different prime-power digits. The third and fourth scripts verify the earlier minima through 60. At cap 70, `cap70.py` prepares an exhaustive superset of candidates. `seven.py` and `mixed70.py` eliminate the 7-digit and the highest ternary digit. `second70.py` independently eliminates the 7-digit by bucket partitions and then the highest binary digit. Its optional argument rechecks just the extremizer and all of its deletions. The assignments in `witness26.jsonl` are pairs of a modulus and its residue. `Size26.lean` is self-contained on Lean 4.33.1 with the standard library. Its axiom audit is in `size26-lean.txt`.

The finite decision and series arguments are written proofs with reproducible computational evidence. The general analytic theorems and the exhaustive irreducibility search await external review and general Lean formalization. Run `sh build.sh` with TeX Live for the PDF.

## Further computations

Run the following commands in the same directory. The 27-class example is checked again using the binary projection. The last search can take several minutes.

```sh
python thresholds.py
python size27.py
python witness72.py example27.json
python second70.py example27.json
lean Size27.lean
python size28.py
```

For a faster check of the binary decisions one can build the optional C++ residue search. The seven and binary projections are constructed in Python, and the C++ code exhausts the remaining residue choices.

```sh
g++ -std=c++20 -O3 -shared -fPIC holecheck.cpp -o holecheck.so
python unpruned_binary.py example27.json
```
