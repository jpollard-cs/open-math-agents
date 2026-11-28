# Single uncovered residues on prime trees

Codex (OpenAI), at Jordan Pollard’s request. AI-authored written mathematics and Lean development for public review, 27 November 2026.

[Manuscript](anchored.pdf) · [LaTeX source](anchored.tex) · [Finite checks](finite-checks.txt) · [Lean verification](verification.txt)

For every sufficiently large exact size k the unrestricted minimum largest modulus beats the best grouped placement by at least cε times the four-fifths power of the grouped minimum. The same construction attains reciprocal sum at least R₀(k)−ε. Grouped placements permit arbitrary disjoint blocks of prime-digit positions, with the largest modulus reserved. Every unrestricted minimizer leaves at least a constant times k^(4/5)/(log k)^(1/5) rows outside its best placement.

In the forest class the sharp surplus in the number of rows at cap X is Θ(X^(4/5)/log X) above Σ_{p≤√X}(p−1), even allowing arbitrary tree depth. At every large exact k the class reciprocal optimum is R₀(k)+o(1). Its excess-producing edges pay a sharp local penalty of at least one eleventh of their actual reciprocal weight. The unrestricted minimum and sharp unrestricted reciprocal coefficient remain open.

A tree of congruence conditions leaves precisely one tuple uncovered. Deleting any ordinary row leaves at least two tuples for every assignment of all surviving residues. A distinguished full-period row can therefore carry all the new primes forward in one substitution. The earlier class that obstructed such a transfer had no separate row for the last tuple.

## Verification

Run the constructors with standard Python 3.10 or later:

~~~sh
python forest_check.py
~~~

They enumerate arbitrary local forbidden cells for three finite trees, including one with two levels of edges, verify the 29-modulus example throughout its integer period of 18,480, and check 63 exact-size stage schedules. The JSON gives the actual congruences.

With Lean 4.33.1 on PATH, first build PacketCoverage, PacketEssential and PacketAssignment in the adjacent [paired-capacity directory](../paired-capacity/), as described in its README. Then from this directory run:

~~~sh
export LEAN_PATH=.:../paired-capacity
lean -o ForestFibre.olean ForestFibre.lean
lean -o StarCoordinates.olean StarCoordinates.lean
lean -s 512000 -o Integer29.olean Integer29.lean
leanchecker -v ForestFibre StarCoordinates Integer29
~~~

ForestFibre.joinValid proves the bottom-up invariant for arbitrary row labels at a node and any finite number of children. Integer29.covering and Integer29.after_deletion apply to actual integers, with complete freedom to reassign every surviving residue. The size, distinct and maximum declarations check 29 distinct moduli with maximum 176. This is a demonstration of period transfer. The known minimum at size 29 is 84. The analytic theorems have written proofs and await independent review.

The graph on the primes is a forest in the main converse. Dense interactions with cycles, particularly those that retain a small set of compulsory continuations after each deletion, deserve separate investigation.

## Cyclic constructions and the unrestricted reciprocal sum

[Four-page proof](cycles.pdf) · [Source and two-terminal converse](cycles.md) · [Full-period transfer principle](transfer.md) · [Cycles sharing one coordinate](joined-cycles.md) · [Interpolation and its exact equality case](interpolation.md)

At every sufficiently large exact size the unrestricted reciprocal maximum exceeds the zero-defect optimum by a fixed additive amount. The lower limit of the difference is at least 0.000704743307. Simultaneously one may retain the four-fifths improvement in the largest modulus if the desired reciprocal gain is any fixed amount below that number. A single cyclic quartet of primes gives a positive exact rational gain, independently checked in Lean. The sharp leading coefficient remains open.

For full-period covers the limiting additive excess is the supremum of explicit finite-prefix gains, possibly infinite. It is finite and positive for the class of cycles joined at one coordinate. The sharp row surplus for those cycles has order X^(3/4)/log X. Product-degree interpolation certificates have a sharp cap surplus of order X^(4/5)/log X and reciprocal ceiling R₀(k)+o(1). The four-prime cycle lies outside that certificate class.

The general proofs are written. [cycle-lean.txt](cycle-lean.txt) records the separate replay of the separator inequality, the binary truth tables and the first quartet's full rational gain. Run the additional checks as follows.

~~~sh
python cyclic_check.py
python diamond_gain.py
python independent_gain.py
python interpolation_check.py
lean -o PathSeparator.olean PathSeparator.lean
lean -o BinaryProfiles.olean BinaryProfiles.lean
lean -o DiamondGain.olean DiamondGain.lean
LEAN_PATH=. leanchecker -v PathSeparator BinaryProfiles DiamondGain
~~~

[Cycle counts and independent sums](cycle-finite.txt) · [Interpolation checks](interpolation-checks.txt)

The direct attempt to replace the chord with arbitrarily many internally disjoint paths fails. A unique continuation through a separating digit forces every endpoint pair differing in both coordinates to extend. The next unrestricted questions are the size of the full-period supremum, the loss on passing from arbitrary covers to full-period prefixes, and blocks that share multiple coordinates. The minimum for general k and the sharp unrestricted reciprocal coefficient remain open.

[Classification for arbitrary binary residual graphs](binary-graphs.md) proves that with two residual digits at every prime and arbitrary parallel pair rows, every one-hole component has a theta core with at least one direct branch and optional pendant trees. The reciprocal gain stays bounded for all such graphs. The multigraph proof credits the related universal satisfiability theorem of Karve and Hirani.

The independent exhaustive graph comparison covers 143 connected simple types and 269 connected multigraph types. Run `python binary_graph_check.py` from this directory. [Results](graph-checks.txt)
