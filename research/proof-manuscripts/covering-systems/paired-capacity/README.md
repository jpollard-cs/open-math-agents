# A power-scale separation for minimum largest covering moduli

Codex, at the request of Jordan Pollard. AI-authored research manuscript for review, 27 November 2026.

[Paper (PDF)](paired-cap.pdf) · [LaTeX source](paired-cap.tex) · [Checked finite construction](Packet6313.lean) · [Zero-defect comparison](Zero6313.lean)

For all sufficiently large exact sizes, even the best zero-defect covering set loses to an explicit irreducible covering set by at least a constant times the three-fourths power of its largest modulus. An unrestricted minimizer has at least a constant times k^(3/4)/(log k)^(1/4) more moduli than the Znám–Simpson minimum for its own period. The construction can at the same time keep its reciprocal sum within any specified positive additive error of the zero-defect maximum. The proof uses paired primes and a fibre contraction valid even when a distinguished modulus is smaller than the ambient period. Section 5 recovers the arithmetic zero-defect cap budget up to an error smaller than every fixed positive power of the cap. Section 6 proves the sharp order of the surplus for full placements in disjoint digit blocks. These general results have written proofs. The unrestricted minimum and sharp unrestricted reciprocal coefficient remain open.

At every size from 6,284 through 6,313 there is a genuine irreducible set with largest modulus 63,252. The zero-defect minimum equals 66,563 at every size from 6,284 through 6,334. The lower exclusion uses the elementary prime-fibre bound and the forced cofactor period at 257. The file plateau.py reproduces all 81 finite constructions. At size 6,313 both actual examples have Lean proofs of all-integer coverage, distinctness, the exact largest modulus, and failure after any deletion with arbitrary fresh assignments of all residues. The analytic estimates and the general implication from the fibre bound to the exclusion are written proofs. No optimality is claimed for the unrestricted example.

## Verification

Python 3.10 or later is sufficient for the constructors. Both forms of packet certificate are verified at every stage against their actual ambient period and distinguished modulus.

```sh
python paired_digits.py
python carried_powers.py 251 307 503
python plateau.py
python make_lean_certificate.py
python make_lean_certificate.py --zero
```

With the official Lean 4.33.1 release on PATH and the directory as the working directory, the following needs only the standard library. PacketCoverage proves coverage for a sequence of residue refinements. PacketEssential proves arbitrary-reassignment essentiality using a pigeonhole argument over every fibre. PacketAssignment constructs one residue function on the distinct integer moduli. Each concrete theorem is replayed by the kernel. The finite budget expression uses trial divisors, primes through 257 and exponents through 17, exhausting the relevant range since 258 squared exceeds 66,563 and 2 to the 17th exceeds the cap.

```sh
export LEAN_PATH=.
lean -o PacketCoverage.olean PacketCoverage.lean
lean -o PacketEssential.olean PacketEssential.lean
lean -o PacketAssignment.olean PacketAssignment.lean
lean -s 512000 -o Packet6313.olean Packet6313.lean
lean -s 512000 -o Zero6313.olean Zero6313.lean
leanchecker -v PacketCoverage PacketEssential PacketAssignment Packet6313 Zero6313
```

[Verification log](verification.txt). The finite examples and general packet lemma are project-independent Lean theorems. The official part (ii) asks for the full unrestricted answer. This manuscript is posted in the contributor fork for review.

## Remaining obstacles and next tests

The construction assigns its side rows to disjoint digit blocks. Mixing overlapping blocks while preserving every row after arbitrary reassignment is necessary to go beyond the proved upper order for this class. The shifted-prime ordering in section 5 fixes all obstructions at any fixed list of prime-power exponents. It leaves the compatibility of preferred orders at growing exponents unresolved.

Separately, the [prime-11 census](../period-budget/prime11-minima.md) restricts the ordinary part of any prospective 49-modulus cover at cap 132. The 38 ordinary moduli must form a noncover. At least three entries beyond the cap-108 pool are necessary, since any 36 ordinary entries from that pool already contain a cover. Thus the set must contain 112, 120 and 126. Among its 35 older entries it needs 32 or 33 from the cap-105 pool. The earlier through-33 census leaves 47 noncovering choices in the first case, including the no-105 set, and one in the second case with three ways to choose two higher entries. We found ordinary covering assignments in ten of these fifty candidates. The [ten certificates](cap132-partial.json) give both the candidate and an explicit subcover. Check them with `python check-cap132.py`. The other forty cases remain unclassified by this pass. A direct full deletion search with the repeated projected 36 made no further decision in this run. These counts do not determine m(49).
