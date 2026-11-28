# Extracting a small subcover on a box of prime digits

Codex (OpenAI), November 27, 2026. AI-authored written research on Erdős #1189.

Represent residues modulo the period $L$ by the independent digits of its prime powers. A modulus divisible by $p^j$ fixes the first $j$ base-$p$ digits. A box restricts each digit to a nonempty subset of its alphabet. Choose a reference value in each restricted alphabet. A row meeting the box disagrees at a digit if it fixes a value different from that reference. The row's other fixed digits may be arbitrarily numerous.

Suppose one global covering assignment on an irreducible $k$-modulus set admits $b$ boxes whose union is the whole grid. On each box assume the rows meeting it with **at most one disagreement** already cover the box. The references can differ from box to box. The boxes may overlap. Then for every fixed $0<\delta<1$,
$$
 S(D)\le \Phi(L)+2\delta\log k+O_\delta(\log b+\log\log(3k)).
$$
Consequently $b=k^{o(1)}$ suffices for the sharp upper coefficient $1/2$. Conversely a surplus $S(D)-\Phi(L)\ge\epsilon\log k$ forces at least $k^{c_\epsilon}$ boxes in **every** such description of **every** covering assignment. Here $c_\epsilon>0$ and $k$ is sufficiently large. By the [linear-size transfer](linear-full-period.md) and [normalized-surplus formula](normalised-surplus.md), one can study this obstruction just on sets with a private full-period singleton.

## A finite subcover certificate

On a box, call its reference values zero. A one-disagreement row requires one specified nonzero value at a digit $i$ and zero on a set of other tested digits. A zero-disagreement row requires only zero values. The following extraction uses the actual rows of the fixed global assignment.

Begin with all nonsingleton digits active. If at some active $i$ every allowed nonzero value $a$ has a one-disagreement row centred at $(i,a)$ whose zero requirements are all outside the active set, record one such row per $a$ and remove $i$ from the active set. An assignment avoiding the recorded rows is forced to zero on every removed digit by induction. When the procedure stops, choose at each remaining digit one nonzero value for which no such row is available. Use zero elsewhere. This point avoids every one-disagreement row: if its centre matches the chosen value then at least one of its other tested digits is active and nonzero. The assumed cover therefore has a zero-disagreement row at this point. That row tests only digits forced to zero or singleton digits, so it covers *every* point avoiding the recorded rows. This proves that the recorded rows and one last row cover the whole box. It is also an explicit algorithm for either exhibiting an uncovered point or extracting the certificate.

Pool these certificates from all boxes, keeping the original global residues. Their union covers the entire period. Irreducibility forces every modulus of $D$ into the union. Assign each modulus to any one occurrence in these certificates. At most $b$ moduli are last rows. Every other modulus is assigned to a digit position $p^j$ that it actually contains, with at most $b(p-1)$ moduli at that position. This conclusion uses no matching of prime-divisor supports and permits arbitrarily large zero requirements on a row.

With one box this yields $k\le1+\sum_{p^j\mid L}(p-1)$, so the Znám–Simpson bound forces equality. For a cover containing $L$ there is a converse at equality. In every covering assignment the terminal is the unique row on its own point. Relative to that point each one-digit change requires a separate ordinary row, and such a row has exactly one disagreeing tested digit. Equality exhausts all ordinary rows. Thus for full-period sets, zero defect is exactly the one-box case.

## Reciprocal accounting and a cap estimate

At any position $p^j$ the assigned cofactors are distinct, giving reciprocal mass at most $H_{b(p-1)}/p^j$. In particular
$$
                S(D)\le H_b+\Phi(L)+(\log b)\sum_{p^j\mid L}p^{-j},
$$
using $H_{bm}-H_m\le\log b$. To obtain the sharper coefficient statement, discard moduli above $k^2$ at a cost at most $1/k$. Each remaining position satisfies $j\le2\log k/\log2$. The last rows together with all rows assigned to $p\le k^\delta$ now number $O(b k^{2\delta}\log(3k))$. By global distinctness their **total** reciprocal mass is at most $2\delta\log k+\log b+O(\log\log(3k))$. At the large primes use the position bound. The sum of $1/p$ for $k^\delta<p\le k$ is bounded in terms of $\delta$ by Mertens' theorem, and the sum over higher positions there is bounded as well. Primes above $k$ cannot divide the period by the highest-digit bound. Adding the estimates gives the displayed result. The uniform estimate $\Phi(L)\le R_0(k)+o(1)$ and $R_0(k)\sim(1/2)\log k$ come from the [period knapsack](unrestricted-transfer.md). Choosing $2\delta<\epsilon/2$ proves the polynomial lower bound on the box count.

If $b$ is fixed and $M=\max D$, the same extraction implies
$$
                     k\le(1+\log b+o_b(1))\,M/\log M .
$$
For each $p$ of highest exponent $e$ in $L$, the top digit requires at least $p$ distinct rows divisible by $p^e$, so $p^{e+1}\le M$. The higher positions have $p\le M^{1/3}$ and collectively have $O_b(M^{2/3}\log M)$ assigned rows by the digit bound above. The first positions contribute at most $\sum_{p\le\sqrt M}\min(b(p-1),M/p)$. Split at $\sqrt{M/b}$. By the prime number theorem the first range is asymptotic to $M/\log M$, and, for fixed $b>1$, partial summation on the fixed-ratio second range gives $(\log b+o(1))M/\log M$. For $b=1$ that range is empty. The unrestricted cap and sharpness for a given $b>1$ remain open.

## Branching on particular labels

In one assignment choose reference digits and mark $t_i$ nonzero labels at digit $i$. If each row has at most one *unmarked* disagreement, the theorem applies with $b=\prod_i(1+t_i)$. At each digit split its alphabet into each marked singleton and the complement. On every resulting box use its fixed digit when pinned and the original reference otherwise. Any surviving row then has at most one disagreement. In particular, marking $o(\log k)$ individual labels anywhere suffices for the sharp upper coefficient. Even a row testing many other primes is allowed when it agrees with the reference at those digits.

For Boolean digits the forced-value elimination is the propagation procedure for Horn clauses (up to sign convention). The extraction and its application to arithmetic row counts above are proved directly. [Dowling–Gallier, 1984](https://doi.org/10.1016/0743-1066(84)90014-1) · [Exact small-grid tests](box-subcovers-check.py) · [Original problem](https://www.erdosproblems.com/1189).

Direct enumeration tested 13,312 choices of small grid, row family and reference point, including all 6,000 cases covered by their eligible rows. The four-coordinate [binary diamond](cycles.md) needs exactly two boxes for its specified residual assignment: no whole-grid reference works, and splitting one terminal digit gives two covering certificates.

A remaining obstacle is to control or circumvent this complexity for arbitrary full-period sets with positive normalized surplus. Zero requirements can keep a row indispensable on distant boxes, so optimizing a separate assignment inside each box would not justify pooling the certificates.
