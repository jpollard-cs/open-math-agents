# The largest active prime at a quadratic modulus cap

[Manuscript](prime-budget.pdf), by Codex (OpenAI) at Jordan Pollard’s request. Prepared for the existing contributor-fork manuscript review, 27 November 2026.

For an irreducible set of exactly k distinct covering moduli, let M be the largest modulus and P the largest prime dividing any modulus. Under M ≤ λk², the largest possible P is asymptotic to min(1, √((1−log 2)λ)) k. Under M ≤ k^σ for 1 < σ < 2, the answer is √((1−log σ)k^σ) to first order. Every lower bound realizes every sufficiently large cardinality, with irreducibility preserved under arbitrary reassignment of residues.

The paper gives an exact integer optimization for the minimum cardinality at a prescribed prime and cap, its asymptotic excess over the prescribed prime, and the sharp density of holes after deleting every multiple of the prime. Without a cap it determines all possible sizes for each sufficiently large prescribed largest prime, as well as the sharp reciprocal maximum through additive o(1) at the first possible size. The overall minimum largest modulus and the unrestricted reciprocal coefficient in Erdős #1189 remain open.

## Reproduction

Run with Python 3. The constructor minimizes cost over compressed prime-exponent lists and builds residues. The independent check solves 94 small instances by separately enumerating all attainable cofactor LCMs. The exact-size program builds examples at sizes 1,000, 5,000 and 10,000 and validates the finite digit data. The output is in checks.txt.

    python constructor.py 11 16
    python independent.py
    python exact_size.py

Lean 4.33.1 checks the 21-modulus construction, all subfamilies and all residue assignments, and separately excludes cofactor cost below ten by a finite exponent check. Build the earlier [integer-substitution modules](../sparse-labels) with their check-lean.sh before running this directory's script. The general extremal and asymptotic results, including the use of Znám–Simpson in the lower bound, have written proofs. Independent human review and priority confirmation are pending.

    sh check-lean.sh
    sh build.sh

## Sources and next obstacle

The formulation of Erdős and Graham, the period inequality of Znám and Simpson, and Dickman's smooth-number theorem are used in the manuscript. The earlier every-size construction is in the [reciprocal-sum manuscript](../reciprocal-sums/erdos1189-reciprocal-sums-and-exact-minima.pdf). Related work on largest modulus and reciprocal sums is due to Öztürk. The prime-digit matching bound gives the upper reciprocal estimate in the final section.

The earlier grid argument sought a contradiction from the complementary rows across many primes simultaneously. Deleting one prime family gives a sharp result even for genuine irreducible covers. The remaining question is what changes when two or more of those prime families must be essential in the same cover. Their individual optimal cofactor periods may share most of their small prime factors.

The last two pages give the joint feasible limits of the largest several primes and the greatest number of large period primes at caps λk log k for fixed λ > 1. A single cofactor period can support all of these prime sections in the same irreducible cover.
