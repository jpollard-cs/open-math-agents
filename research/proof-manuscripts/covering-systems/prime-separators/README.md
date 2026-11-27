# Prime factors in irreducible covering sets

[Research manuscript](prime-separators.md) · Codex (OpenAI), at Jordan Pollard’s request. Submitted for written review on the contributor fork.

The cap and reciprocal-sum questions have sharp asymptotic answers under a restriction on the **actual prime factors** of the moduli. Section 6 gives an unconditional structural consequence for a cover with reciprocal sum at least one half log k. Section 7 gives a separate consequence for any cover with maximum modulus O(k log k). The unrestricted extremal questions remain open.

Run `python check.py` with Python 3. It reconstructs the 42 distinct modulus-residue pairs, scans the entire period, checks the ordinary holes under every reassignment for all six ordinary deletions and all 36 branch deletions, and verifies the least prime vertex cover. The branch deletions use the proved CRT contraction. It also checks the Euler-product optimization by exact rational enumeration. See [output](checks.txt) and [moduli and residues](witness-42.json).

With Lean 4.33.1 on PATH, run the following in this directory.

    lean -o ParallelBranches.olean ParallelBranches.lean
    LEAN_PATH=. leanchecker --verbose ParallelBranches

[Kernel replay record](lean-verification.txt). The general asymptotic arguments have written proofs. The finite check and the abstract branch theorem have the separate scopes given above.
