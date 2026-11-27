# Which pairs of holes can the same prime cover?

Codex (OpenAI), at Jordan Pollard’s request. Supplement to the [prime-support manuscript](prime-separators.md).

Fix a prime p whose highest digit in the period has p possible values. Write the full period as Bp, with p-adic exponent one higher than in B. Every congruence that uses this digit has modulus p e_i, where e_i divides B and its p-adic exponent is the full one in B. There may be repetitions in the list of t projected moduli e_i, as can happen after a contraction. Every other row depends only on the base point modulo B. A top row chooses one class modulo e_i and one of p digit values independently: this follows by taking the usual base-p digits for the p-part and CRT for the other prime powers.

For **any two specified base points** x and y, some assignment of the t top rows covers all lifts of both points if and only if
$$
 t\ge p,\qquad \#\{i:e_i\mid x-y\}\ge\max(0,2p-t).
$$
For each digit choose a covering row over x and one over y. The p distinct choices on each side have at least 2p−t indices in common, all of which must project onto both points. Conversely choose s=max(0,2p−t) compatible indices. Assign them to both points for s different digits. For every other digit give it a separate row at each point. There are enough unused rows, since 2p−s≤t. This also handles x=y and t≥2p. No individual residue assignments have been fixed in this equivalence.

This decides the strongest universal congruence condition on **all** base points whose fibres are fully covered. Write t=p+a with 0≤a<p. For each prime q, sort the t valuations v_q(e_i) in decreasing order and take the (2a+1)-st entry. Let D be the product of these prime powers, with factors of exponent zero omitted. In every assignment, all fully covered base points belong to one class modulo D, if there are any. This holds for a modulus d dividing B in every assignment **if and only if** d divides D.

Indeed a difference of two such points must be divisible by all entries of some subset of size p−a. The gcd of the LCMs of these subsets is precisely D: a power q^j divides all those LCMs exactly when at least 2a+1 projected entries contain it. Conversely the difference equal to any such subset LCM is realized modulo B by the two-point equivalence, so any universally forced divisor of B divides their gcd. At t=p this recovers the usual single-class LCM contraction. At t≥2p no nontrivial congruence is forced by the top rows alone.

For distinct top moduli the projected e_i are distinct. Consequently distinct ordinary holes at distance u require at least 2p−t **different divisors** of u among the e_i whenever t<2p. In particular no two holes can be consecutive if t≤2p−2. All these restrictions apply to any covering assignment of the entire system. Showing that its other rows must leave such an incompatible pair would rule out a candidate even when the universal divisor D is one.

There is a quantitative price for forcing a given modulus d. Each full prime power dividing d must occur in at least 2a+1 cofactors. Hence
$$
 d^{2a+1}\mid\prod_i e_i,\qquad
 d\le (M/p)^{t/(2a+1)} .
$$
In particular, if one tries to replace an exterior row of very large modulus by more than p rows at the same prime and still force all holes into its one class under arbitrary reassignments, this bound can preclude the proposed substitution. A different interaction with the remaining rows could still preserve irreducibility.

For **three or more specified sites** there is an exact finite algorithm. Normalize the sites modulo B. For each e_i list their nonempty residue classes modulo e_i as subsets of sites. For one digit, a subset I of rows suffices precisely when one listed subset per row can cover all the sites. Compute the inclusion-minimal such I by finite union. All p fibres are covered at the sites precisely when one can pack p pairwise disjoint sufficient row sets. Necessity partitions the available rows by their chosen digit. Sufficiency assigns one such set to each digit and combines its residue choices. This formulation keeps the row assignments consistent across all sites.

For example, take p=2, B=9, e=(1,3,9), giving the three distinct top moduli 2,6,18. Every pair among base points 0,1,2 can be covered completely, since the single cofactor 1 passes the pair test. The triple cannot: whichever digit omits the cofactor-1 row has only the other two rows, each of which can hit only one of these three sites. Thus pair tests, even all at once on the same candidate set of holes, need not certify a simultaneous assignment. The accompanying program compares the two-point criterion and strongest common modulus with brute-force residue-and-digit assignments on small periods, including the triple obstruction.

The pair criterion and the valuation rule are written proofs. The tests are finite. Neither gives an unrestricted lower bound on the largest modulus without information on the holes left by the complementary rows.

## Simultaneous test for two different prime digits

The two-site argument can eliminate two prime digits jointly. This uses rows that fix *both* digits, the case where exterior prime branches cannot be treated independently. Choose two distinct active primes p,q, and remove their highest digits to form the base. Fix two base sites x,y. A row that involves at least one deleted digit has type P, Q, or PQ according to which digits it fixes. Its projection is a class modulo the original modulus divided by p, q, or pq respectively. An index is compatible if its projected modulus divides x−y. All other rows, which involve neither top digit, are considered ordinary. The following test asks whether the top rows alone can fill both p-by-q fibres.

Let a,b be the number of compatible and incompatible type-P rows. Define c,d likewise for type Q. Let t be the total number of PQ rows and g their compatible count. For integers 0≤i≤b and 0≤j≤d put
$$
 U=(p-a-i)_+,\quad U'=(p-a-b+i)_+,\qquad
 V=(q-c-j)_+,\quad V'=(q-c-d+j)_+.
$$
There exists an assignment filling both prescribed fibres **if and only if**, for some i,j,
$$
 t\;\ge\;UV+U'V'-\min\{g,\min(U,U')\min(V,V')\}.
$$

For necessity allocate the incompatible single-digit rows between the sites according to where they are active, assigning unused ones arbitrarily. At least U and U′ column values, and V and V′ row values, respectively, are then still missing. Select exactly that many genuinely missing values at each site; their two Cartesian rectangles require UV and U′V′ cell hits. A PQ row can supply two of these hits only if compatible and its cell occurs in both rectangles. Their overlap has at most min(U,U′)min(V,V′) cells. This gives the lower bound even if an assignment wasted some of its single-digit rows.

For sufficiency use the compatible P rows on a common initial segment of column values, up to saturation. Allocate i of the other P rows to x and the rest to y, extending the initial segment at each site. Ignore extras after saturation. Perform the same construction on row values. The two rectangles of missing cells now intersect in *exactly* min(U,U′)min(V,V′) cells because each coordinate's missing sets are nested. Use a compatible PQ row at each of as many common cells as possible, up to g. The remaining slots may serve individual outstanding cells even if they happen to be compatible. The inequality gives enough distinct rows. Digit and exterior residues can be prescribed independently for an individual row by the prime-power coordinate representation. This proves the exact criterion, including empty or unequal rectangles.

For example, take p=5,q=7 with two P rows, three Q rows and seven PQ rows over a single base point. Their total densities on that fibre sum to 36/35, and both primes pass the separate necessary count of top rows. Yet the two uncovered coordinate sets have sizes at least three and four, so twelve individual cells must be filled and seven cannot suffice. The formula covers the two-site case as well. It gives a finite decision procedure of O((b+1)(d+1)) arithmetic tests once the row types are counted. It does not decide the unrestricted optimization over whole modulus sets.
