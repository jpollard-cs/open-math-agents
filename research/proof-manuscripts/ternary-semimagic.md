# Signed permutation decompositions of ternary semi-magic squares

A square matrix over $\mathbb F_3$ is *semi-magic* if all its row sums and column sums have one common value, called its *margin*. Let $\beta(A)$ denote the least number of distinct permutation matrices in an expression for $A$ as a linear combination over $\mathbb F_3$. Each nonzero coefficient is $+1$ or $-1$. Write $M(n)$ for the largest value of $\beta(A)$ among the semi-magic squares of order $n$.

**Theorem.** For every $n\ge1$,
$$
M(n)\le\left\lceil\frac{3n}{2}\right\rceil .
$$
For all $n\ge6$ the sharper bounds
$$
4\lfloor n/3\rfloor\le M(n)\le2\lceil2n/3\rceil+1
$$
give $M(n)=4n/3+O(1)$. Among squares of margin zero, the maximum is exactly $4n/3$ whenever $3\mid n$ and $n\ge6$.

The first inequality answers the third question in Gerry Myerson's MathOverflow post of 11 August 2025. The argument constructs integer lifts with controlled line sums, decomposes them into signed perfect matchings, and checks the case $n=4$ by a finite enumeration. [Myerson's question](https://mathoverflow.net/a/499014)

## 1. Passing from an integer lift to permutations

Call a row or column a *line*. Suppose an integer matrix $B$ reduces to $A$ modulo three, and each line of $B$ has the same integer sum $d$. Write $B=B^+-B^-$ for its nonnegative positive and negative parts. Let $P$ be the largest line sum of $B^+$. Each line of $B^-$ consequently has sum at most $P-d$.

Add the same nonnegative integer matrix $E$ to both parts until every line of $B^++E$ sums to $P$. Such an $E$ exists because the total row deficit equals the total column deficit. Repeatedly fill an entry by the smaller of its row and column deficits until all deficits vanish. Now each line of $B^-+E$ sums to $P-d$. A nonnegative integer matrix with common line sum $b$ is the sum of $b$ permutation matrices. For $b>0$ its bipartite multigraph is $b$-regular, so Hall's condition holds by counting edges from any set of rows. Remove a perfect matching and iterate. Hence
$$
                              \beta(A)\le 2P-d .
$$
Repeated permutations may be combined over the field.

## 2. A rounding lemma

Write each residue as $a\in\{0,1,2\}$. The two allowed integer lifts of one cell will be $a$ and $a-3$. A fractional choice $y$ assigns mass $y$ to the first lift and $1-y$ to the second. Suppose $0\le y_{ij}\le1$ and the sum of the $y_{ij}$ on each line is integral (the sum can depend on the line).

There is a choice $Y_{ij}\in\{0,1\}$ preserving each of these line sums exactly. Moreover, separately on each line and for each of the three residue classes $a$, the sum of $Y$ over cells of that class lies between the floor and ceiling of the corresponding sum of $y$.

To see this, send flow from a source through row vertices, then through a separate vertex for each row and residue, then along unit-capacity cell arcs to column-and-residue vertices, then through the column vertices to a sink. Prescribe the integral line sums on the source and sink arcs. Give the arcs between a line and its residue vertices the floor and ceiling just stated as lower and upper capacities. Add a return arc from sink to source carrying the total prescribed flow. The $y_{ij}$ give a feasible circulation. Integral circulation follows from the integral max-flow theorem. Subtract the lower bounds, join the resulting imbalances to a supersource and supersink, and take an integral maximum flow. Fractional feasibility ensures that this flow saturates all the required arcs. Its cell arcs give the claimed $Y$. Taking $a$ where $Y=1$ and $a-3$ elsewhere produces an integer matrix.

## 3. The zero-sum bound

First suppose the common line sum of $A$ is zero in the field. Put $y=(3-a)/3$ in each cell, so its fractional signed value is zero. On each line $\sum y=n-\sum a/3$ is an integer, and rounding gives common signed line sum zero.

Consider a line with $u$ ones and $v$ twos. All its zeros stay zero. If $x$ ones are flipped to $-2$ and $w$ twos are flipped to $-1$, the signed margin condition gives $x+w=(u+2v)/3$. The positive mass of the line is therefore
$$
 (u-x)+2(v-w)=\frac{u+2v}{3}+x
 \le \frac{u+2v}{3}+\left\lceil u/3\right\rceil
 = \left\lceil\frac{2(u+v)}{3}\right\rceil .
$$
The rounding lemma supplies the inequality, since the expected number of flipped ones is $u/3$. Part 1 now shows $\beta(A)\le2\lceil 2n/3\rceil$. For arbitrary common sum $s$, the matrix $A-sI$ has zero common sum. Restoring $sI$ yields
$$
                  M(n)\le 2\lceil 2n/3\rceil+1.
$$
For every integer $n\ge9$, as well as $n=3,6,7$, the last expression is at most $\lceil3n/2\rceil$. This follows directly for $n=3,6,7,9,10,11,12,13,14$; increasing $n$ by six increases the two sides by eight and nine, respectively.

## 4. The exceptional orders

At orders five and eight the zero-sum bound already suffices for matrices of common sum zero. Negating the matrix if necessary reduces every remaining case to common sum one. Use instead the fractional choice
$$
                           y=\frac{3-a-2/n}{3}.
$$
It lies between zero and one. Its fractional signed value is $-2/n$ per entry. On a line with $u$ ones, $v$ twos, and $z=n-u-v$ zeros, the total retained count is the integer $t=n-(u+2v+2)/3$. The rounded matrix therefore has common signed margin $d=-2$.

Write $Y_0,Y_2$ for the numbers of retained zeros and twos on this line. Its positive mass is $t-Y_0+Y_2$. The fractional bounds give
$$
 t-Y_0+Y_2\le t-z+\mathbf1_{z>0}+
                       \left\lceil\frac{(n-2)v}{3n}\right\rceil
 \le \left\lfloor\frac{2(n-z)}3\right\rfloor+\mathbf1_{z>0}
 \le \left\lfloor\frac{2n+1}3\right\rfloor .
$$
The first inequality uses $\lfloor z(1-2/(3n))\rfloor=z-\mathbf1_{z>0}$. For the second, bound the ceiling by $\lceil v/3\rceil\le(v+2)/3$ and use integrality. Thus $P\le3$ at $n=5$ and $P\le5$ at $n=8$. Part 1 gives eight and twelve terms respectively, as required.

At $n=1$ and $2$ the matrix needs at most one or two terms. In the second case each valid matrix has diagonal entries equal and off-diagonal entries equal. At $n=4$ an exhaustive certificate gives maximum six. The following recurrence specifies the finite proof in full. Start with $S_0=\{0\}$ and set
$$
 S_{j+1}=S_j\cup\{A+P,A-P:A\in S_j,\ P\text{ one of the 24 permutation matrices}\}
$$
over the field. The counts at *minimum* distance $j=0,\ldots,6$ are
$$
                   1,\quad48,\quad996,\quad10400,\quad37540,\quad10016,\quad48.
$$
Their sum is $59049=3^{10}$, the number of semi-magic squares. Indeed the nine entries in the upper left corner together with the common margin determine and freely parametrize a square, since the bottom-right requirement from its row agrees with that from its column. The appendix gives a complete Python implementation. Distance in this recurrence equals $\beta$. Repeated occurrences of a permutation combine into a single ternary coefficient, and any expression supported on $j$ distinct permutations gives a path of length $j$. This finishes the proof for all positive orders.

## 5. The optimal leading constant

Choose $m\ge6$ divisible by three and form an $m\times m$ matrix with three rows entirely one and all remaining rows entirely two. Each row sum and each column sum vanishes modulo three. In an expression with $a$ positive permutations and $b$ negative permutations, any cell of residue one with $p$ positive and $q$ negative hits obeys $2p+q\ge2$. Indeed either $p\ge1$ or $q\equiv2\pmod3$. Likewise at a cell of residue two, $p+2q\ge2$. Sum the first inequality over an all-one row and the second over an all-two row. Each permutation hits each row once. Thus
$$
                2a+b\ge2m,\qquad a+2b\ge2m,\qquad a+b\ge4m/3.
$$
The zero-margin upper bound gives equality for this matrix. For general $n\ge6$, embed the example for $m=3\lfloor n/3\rfloor$ in the upper left of an $n\times n$ matrix, filling the border with zeros. It remains semi-magic. On summing over the first $m$ positions of the two special rows the same inequalities persist, because each permutation hits those positions at most once. We obtain
$$
    4\lfloor n/3\rfloor\le M(n)\le2\lceil 2n/3\rceil+1
       \qquad(n\ge6).
$$
In particular the coefficient $4/3$ is sharp. Among zero-margin matrices it gives the exact worst case at every multiple of three of size at least six.

## Appendix. A finite certificate for order four

Each state below stores disjoint bitmasks for the cells of residues one and two. Adding a permutation cycles the three residues on its mask. Subtracting it cycles them in the other direction. Starting with the zero matrix, the program checks the number of newly reached states at every distance and the total number of states.

```python
from itertools import permutations

masks = [sum(1 << (4*i+j) for i, j in enumerate(p))
         for p in permutations(range(4))]
front = seen = {(0, 0)}
for expected in [48, 996, 10400, 37540, 10016, 48]:
    adjacent = set()
    for a, b in front:
        for m in masks:
            c = m & ~(a | b)
            adjacent.add(((a & ~m) | c, (b & ~m) | (a & m)))
            adjacent.add(((a & ~m) | (b & m), (b & ~m) | c))
    front = adjacent - seen
    assert len(front) == expected
    seen = seen | front
assert len(seen) == 3**10
```

