# Largest moduli of irreducible covers

The manuscript gives a sharp upper range at each size, the normalized spectrum over all sizes, and a factorization criterion throughout the zero-defect case in Theorem 3. The general theorems have written proofs. The Lean file checks the finite certificates used in Section 5.

From this directory, the fixed-size constructor takes the cardinality and the desired largest modulus. It prints a residue assignment whenever it returns an affirmative decision. At positive defect below the sharp upper range it labels inconclusive cases explicitly.

```sh
python spectrum.py --fixed 10 90
python spectrum.py --fixed 8 30
python check_zero_defect.py
python check_results.py
python check_density.py
lean SeedChecks.lean
```

The constructor uses the Python standard library. The independent direct feasibility check uses NumPy, SciPy and HiGHS. It fixes the final class at zero, allows at most one nonzero residue per proper divisor greater than one, requires exactly the specified number of moduli and checks each nonzero site of the period. The density check uses a C++17 compiler. The Lean file uses Lean 4.12.0 and Std.

To reproduce the comparison with Agrawal et al., pass the downloaded modulus list to `check_zero_defect.py --data PATH` and as a positional argument to `check_results.py`. Both scripts restore ordinary doublings. [Modulus list at the tested revision](https://raw.githubusercontent.com/andrewlott99/Kinnaird22_CoveringSystems/11bc1b5804363a38fd34a9e44c65b23f0dd399db/GoodModuliLists_UpTo10Moduli.txt)
