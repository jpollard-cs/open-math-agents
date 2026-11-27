# Optimal periods, prime squares, and exact minima through 30 moduli

Codex (OpenAI), at Jordan Pollard’s request. Public research manuscript for review, 27 November 2026.

[Read the paper](period.pdf). Its first two sections evaluate the arithmetic divisor maximum in Section 8 of Ege Öztürk’s preprint, through its constant term. For the explicit smooth-number envelope they also determine the first term of the vanishing difference and the optimal prime-square threshold. Coverage alone eventually costs zero in the arithmetic problem. The paper links the additive cost of irreducibility to the largest modulus. The leading unrestricted upper coefficient belongs to Öztürk. The companion thread supplied the ten minima through cardinality 25 and the stronger error in the defect interpolation.

For the relaxed period problems the largest prime raised to power $j$ has different sharp thresholds for maximizing reciprocal mass and minimizing the largest selected divisor. Section 2 proves both thresholds for every fixed $j$, along with the sharp cost of the cutoff in either calculation. The two arithmetic objectives eventually require different periods.

At size 26 the minimum largest modulus is 70. The finite search finds exactly one extremal modulus set. Two decision procedures check the positive example and the impossibility of a cover after every deletion with all residues freely reassigned. The residue assignment also has a stand-alone Lean check for every integer. At size 27 the minimum is 72, with exactly three extremal sets. Both sizes 28 and 29 require exactly 84. The 29-element optimum is unique. Size 30 requires exactly 96. The unrestricted sharp reciprocal coefficient and the general minimum largest modulus remain open.

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

## The cap-84 witnesses

Use `size28.py` or the compiled `reverse80.py` to exclude smaller maxima at size 28. `size29.py` uses the recorded reversed 35-case output. `size28_84.py` includes the successful 28-element witness among the sets with exactly four of the five added moduli. The [completed census](cap84-census.md) lists both 28-element minimizers, including the one with all five new moduli. Build `holecheck.so` as above for the cap-84 scripts.

```sh
python reverse80.py > size28-reverse.txt
python size29.py > size29-results.txt
python size28_84.py > search28_84.txt
python witness84.py examples28_84.json
python witness84.py size29-yes.json
python binary84.py examples28_84.json
python binary84.py size29-yes.json
```

At cap 90 there are exactly two 30-set candidates remaining after subset tests. Both fail to cover. Run `size30.py` with the previous results in place, or compile `maskcombine.cpp` and run `quick30.py` to evaluate the two whole-set decisions first. The constructive bound at 96 replaces a modulus 48 in the 29-set by 32 and 96.

```sh
g++ -std=c++20 -O3 -fPIC -shared maskcombine.cpp -o maskcombine.so
python quick30.py
lean Size28.lean
lean Size29.lean
lean Size30.lean
```

The [size-31 analysis](cap96-fibres.md) reduces the next minimum to 96, 105, or 108. Its residue construction and the second size-28 example have stand-alone Lean files.

Reproduce the completed size-28 census, independent digit order at sizes 28 and 29, and the size-31 mask audit with the commands below. Both native libraries are built from the sources in this directory.

```sh
g++ -std=c++20 -O3 -fPIC -shared holecheck.cpp -o holecheck.so
g++ -std=c++20 -O3 -fPIC -shared maskcombine.cpp -o maskcombine.so
python classify28.py
python binary90.py all-five-extremizers-28.json
python binary90.py size29-yes.json
python check_cap96.py
lean Size28Second.lean
lean Size31Upper.lean
```

## Sizes 31 through 33

The [new census and proof](minima-31-33.md) give $m(31)=96$ and $m(32)=m(33)=108$. There are precisely two minimizing 31-element sets. The note links the residue witnesses, Lean proofs of coverage and cardinality, and the exhaustive decision procedure for freely reassigned residues.
