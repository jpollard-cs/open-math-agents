# The repeated modulus at size 31

Any 31-element candidate at maximum 96 must contain 32 and 96. Through 95 it could use only six moduli outside the cap-60 pool, and every 25-element subset of that pool already covers. A singleton top binary row is redundant. Contracting 32 and 96 produces a virtual modulus 48. If 48 were absent beforehand, this would give an irreducible 30-element set of distinct moduli at maximum at most 90. Thus all three of 32, 48, 96 are required. After contraction there are two distinguishable rows of modulus 48.

When 16 and 80 are both present, the four rows fixing the next highest binary digit have projected moduli 8, 24, 24, 40. There are just two kinds of maximal allowable hole masks below that digit.

* On one residue class modulo 8, take the union of two distinct classes modulo 24 and one class modulo 40, all lying in that class modulo 8.
* On two different residue classes modulo 8, take a class modulo 24 on one and a class modulo 40 on the other.

For the first pattern put modulus 8 on one side (one value of the new digit), and 24, 24, 40 on the opposite side. For the second, pair 8 and 40 over the 40-class, one per side, then use one of the two 24-rows on each side over the 24-class.

Conversely a point allowed below the digit must be covered on both sides. All four projected moduli are multiples of 8. A supported 8-class needs at least two rows, so at most two such classes are supported. With one supported class, consider the side opposite the 8-row. Its allowed set is contained in the union of the two 24-classes and the 40-class inside that 8-class. Missing or repeated classes may be extended to the full first pattern without affecting any other fibre. With two supported 8-classes, exactly two rows serve each and their intersection is either empty or a class modulo their least common multiple. Pairing 8 with 40 leaves the two 24-rows together, yielding the second pattern. Pairing 8 with a 24-row leaves 24 with 40, hence gives a 24-class and a 120-class; the latter is contained in a 40-class on its own 8-class. This exhausts the pairings.

The families can be used as two virtual-row types on the 120-cycle below the ternary digit. When 16 or 80 is absent use the actual sublist of projected moduli and the same two-bucket rule. This classification does not by itself decide whether a size-31 cover attains 96.

There is also an upper bound of 108 at size 31. Use the explicit 29-set at maximum 84 and replace 36 by 27, 54, 108. The three new moduli alone fix the highest ternary digit, and their projections 9, 18, 36 have least common multiple 36. The saturated three-row contraction gives exactly the old cover. Deleting a new entry forces the lower rows alone to cover, and deleting an old entry contracts to the corresponding old deletion. This proves irreducibility with all residues free. From 97 through 107 the only new eligible modulus is 105. Thus the size-31 minimum is one of **96, 105, 108**.

The file `check_cap96.py` checks all 3,929 attainable projected masks, including all translates, and finds exactly 960 distinct maximal masks of the two stated types.

The explicit residue assignment in `witness31-upper108.jsonl` covers the full period of 15,120. The self-contained `Size31Upper.lean` checks coverage of every integer, cardinality, distinctness, and maximum. Irreducibility follows from contraction and the size-29 deletion checks above.
