# An infinite defect-one family for Erdős #1189

## Result

For every integer `e >= 2`, put

\[
 S_e=\{2,3,5,6,10,15\}
 \cup\{2\cdot3^j:2\le j\le e\}
 \cup\{10\cdot3^j:1\le j<e\}
 \cup\{3^e,5\cdot3^e\}.
\]

**Theorem.**  The set `S_e` is an irreducible covering set.  It has
`2e+6` distinct moduli and largest modulus `5*3^e`.  Consequently its
defect relative to the Simpson cost of its largest modulus is exactly one:

\[
 (|S_e|-1)-\sum_{p^a\parallel 5\cdot3^e}a(p-1)
 =(2e+5)-(2e+4)=1.
\]

This proves the candidate family in the earlier computational checkpoint for
all `e`, and supplies infinitely many odd composite largest moduli in the
first layer beyond the zero-defect classification.  It is a partial result on
Erdős problem #1189, not a solution of its general extremal questions.

The argument was produced by an AI research agent at Jordan Pollard's request.
The proof is written below and the accompanying checker independently expands
the recurrence through finite periods.  Priority and external review are not
known.

## 1. The six-point replacement lemma

Let `R` be a positive odd integer, `Q=10R`, and `L=3Q`.  Suppose a covering
system of `Z/QZ` contains the two classes with moduli `R` and `5R`, and that
deleting precisely these two classes leaves exactly two uncovered points
`a != c` modulo `Q`.

Lift every remaining class unchanged to `Z/LZ`.  Its uncovered set is

\[
 \{a,a+Q,a+2Q,c,c+Q,c+2Q\}.
\]

Add the four classes

\[
 a\pmod Q,\qquad
 c\pmod {3R},\qquad
 c+Q\pmod {6R},\qquad
 c+2Q\pmod {15R}. \tag{1}
\]

The first covers the three lifts of `a`; the other three cover the displayed
three lifts of `c`, respectively.  Indeed no class among the latter three
contains either of the other two assigned lifts: a nonzero difference among
them is `Q` or `2Q`, and neither is divisible by `3R`, `6R`, or `15R` as
appropriate.  Thus (1) completes a cover of `Z/LZ`.

If the new classes of moduli `3R` and `15R` are deleted, exactly `c` and
`c+2Q` are uncovered.  This is the same two-hole hypothesis at the next
scale.

There is also a useful fixed-residue irredundancy statement.  Every old class
that remains has a private point `x` distinct from `a,c`.  Its three lifts can
be hit by the new classes of moduli `3R,6R,15R` only when, respectively,

\[
 x\equiv c\pmod R,\qquad
 x\equiv c\pmod {2R},\qquad
 x\equiv c\pmod {5R}.
\]

All three conditions would imply `x=c mod lcm(R,2R,5R)=Q`, which is false.
The class modulo `Q` does not hit a lift of `x`, either.  At least one lift of
`x` therefore remains private.  The same argument with `x=a` gives a private
point for the new class modulo `Q`, and each of the other three new classes
has its assigned lift of `c` as a private point.

## 2. The seed and induction

At `e=2`, use the following residue assignment, listed as `residue (mod
modulus)`:

\[
\begin{array}{c|rrrrrrrrrr}
\text{modulus}&2&3&5&6&9&10&15&18&30&45\\
\hline
\text{residue}&1&1&4&2&0&8&0&6&6&12.
\end{array}
\]

A check modulo `90` shows that these classes cover every residue.  Deleting
the classes modulo `9` and `45` leaves exactly the two points `72` and `12`.
Each displayed class has a private point; these finite assertions are also
checked by the companion script.

Now suppose the construction has reached `S_{e-1}`.  Its period is
`Q=10*3^(e-1)`.  Set `R=3^(e-1)` and apply the lemma.  The retained moduli are

\[
 S_{e-1}\setminus\{3^{e-1},5\cdot3^{e-1}\},
\]

and the four added moduli are

\[
 3^e,\quad 2\cdot3^e,\quad10\cdot3^{e-1},\quad5\cdot3^e.
\]

Their union is exactly `S_e`.  The lemma gives a cover, two new distinguished
holes after deleting the new pure moduli, and a private point for every
class.  This proves by induction that a displayed irredundant covering system
exists on `S_e` for every `e>=2`.

## 3. Why the modulus set itself is irreducible

Private points only prove irredundancy for the displayed residues.  Erdős
#1189 uses the stronger notion: no proper subset of the moduli may cover after
all residues are reassigned.  Simpson's lower bound supplies the bridge.

Assume a proper subset of `S_e` is a covering set and delete redundant
classes from one of its covers.  The resulting irredundant covering system
has LCM

\[
 M=2^\alpha3^\beta5^\gamma,
 \qquad \alpha,\gamma\in\{0,1\},\quad0\le\beta\le e,
\]

and Simpson's theorem requires at least

\[
 1+\alpha+2\beta+4\gamma \tag{2}
\]

classes.

Let `N(alpha,beta,gamma)` count the members of `S_e` that divide `M`.  If
`beta=0`, then

\[
 N=\alpha+\gamma+\alpha\gamma<1+\alpha+4\gamma.
\]

If `1<=beta<e`, direct counting of the six base moduli and the two chains
gives

\[
 N=1+\alpha(\beta+1)+2\gamma+
       \alpha\gamma(\beta+1).
\]

Checking the four pairs `(alpha,gamma)` shows that this is strictly smaller
than (2).  (For `(1,1)` the two quantities are `2 beta+5` and `2 beta+6`;
the other three cases have a larger gap.)

Finally, if `beta=e`,

\[
 N=2+\alpha(e+1)+3\gamma+\alpha\gamma e.
\]

This is strictly smaller than (2) except at `(alpha,gamma)=(1,1)`, where
both equal `2e+6=|S_e|`.  Therefore an irredundant covering subsystem must
have the full LCM and at least every one of the `|S_e|` available moduli.  It
cannot be a proper subset.  Hence `S_e` is an irreducible covering set.

## 4. Verification and status

`check_defect_one_family.py` constructs the residue systems recursively and
checks, for `2<=e<=10`, full coverage, the two-hole invariant, and a private
point for every displayed class.  It separately enumerates every possible
LCM divisor pattern and verifies the strict Simpson-count inequality, with
equality only at the full period.  These are finite checks of the identities
used above; the theorem for all `e` follows from the written induction.

The literature check used the current Erdős #1189 page, Simpson's bound as
quoted there, Sun's divisor-family result, and the 2024 work of Balister,
Bollobás, Morris, Sahasrabudhe and Tiba.  The search did not locate this
specific `5*3^e` family or the replacement lemma.  That is not a priority
claim, and independent mathematical review is still needed.
