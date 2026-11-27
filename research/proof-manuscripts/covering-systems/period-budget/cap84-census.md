# The two optimal 28-modulus sets

Codex (OpenAI), at Jordan Pollard’s request. Computational supplement to the period-budget manuscript. Research version for review.

An irreducible set of moduli covers the integers with one residue per modulus. Deleting any one modulus destroys the possibility of coverage even if every residue may be reassigned. At size 28 the minimum largest modulus is 84. There are exactly two sets of moduli attaining it. With

$$P=\{2,3,4,5,6,7,8,9,10,12,14,15,16,18,20,21,24,28,30,35,36,40,42,45,48,56,60,63,70,72,80,84\},$$

the sets are obtained by deleting respectively $\{2,3,8,63\}$ and $\{2,4,8,12\}$ from $P$. This counts sets of moduli. It permits different assignments of residues to a given set.

## Exhaustion

By the prime-power eligibility bound in the paper, $P$ is the entire pool at 84. Write $E=\{63,70,72,80,84\}$ for the five moduli added above the old 27-element pool. Every 25-element subset of the old pool is coverable, so a candidate needs at least four members of $E$. It includes 84 by the strict lower bound at size 28.

With exactly four new moduli there are only 35 noncoverable old 24-sets. For each possible omitted new modulus, the finite solver tests these choices. It discards an isolated highest binary row, tests the single deletions with all residues free, and tests coverage of the full set when necessary. The first displayed extremizer is the only survivor. See `size28_84.py` and `search28_84.txt`.

With all five new moduli choose 23 old entries. Remove any case where those entries already cover, where the full set has a single highest binary row, or where the full set is a proper subset of the recorded irreducible 29-set. These exclusions leave 741 distinct candidates. In 597 cases an explicit single deletion is coverable. A further 143 whole sets fail to cover. The remaining candidate is the second displayed extremizer. The script `classify28.py` reproduces this branch. The file `cap84-final-audit.json` lists the 741 sets by the four omitted old entries, together with the removable modulus when one exists. Both the first and the last exclusion are valid with arbitrary reassignment: coverability is upward closed and the 29-set is irreducible in this stronger sense.

The assignments in `witness28.jsonl` and `witness28-second.jsonl` cover all 5,040 residues of the common period. The Lean files `Size28.lean` and `Size28Second.lean` lift this to all integers and certify size, distinctness, and maximum. The exhaustiveness and irreducibility claims use the separate finite-search proof. The distinct elimination order in `binary90.py` also checks the second covering set and every single deletion. The analogous check of the unique size-29 optimum is in `independent29-native.txt`.

The same [supplement for size 31](cap96-fibres.md) gives a constructive upper bound and identifies the three surviving values for the next exact minimum. External review of both supplements is pending.
