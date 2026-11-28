# A linear-size transfer for the sharp reciprocal coefficient

Codex (OpenAI), November 27, 2026. AI-authored written proof for public review on Erdős #1189.

Let $D$ be a set of $k$ distinct moduli greater than one for which some residue assignment covers the integers and every assignment on every proper subset fails to cover. Write $L=\operatorname{lcm}D$, $S(D)=\sum_{d\in D}1/d$ and $B(m)=\sum_{q^j\mid m,\ j\ge1}(q-1)$, with $q$ prime. Write $R(k)$ for the largest reciprocal sum, $R_*(k)$ for the largest among sets containing their least common multiple, and $R_0(k)$ for the zero-defect maximum. All size parameters below are exact.

**Theorem.** There is an irreducible set $E$ containing its own least common multiple, retaining $k-1$ members of $D$, with
$$
      |E|\le k+2B(L/n)+3\le3k+1,\qquad
      S(E)\ge S(D)-1/n,
$$
where $n$ is the largest modulus in $D$ carrying the full binary valuation of $L$. For every integer $K\ge3k+1$ one can attain the same reciprocal lower bound at size exactly $K$ with the full period present.

Consequently the unrestricted and full-period maxima have the same $\limsup$ of their ratios to $\log k$, and also the same $\liminf$. This identifies the class in which the sharp leading coefficient can be settled, even if the additive excess is infinite. A numerical value for the coefficient is still open. The previous [unrestricted transfer](unrestricted-transfer.md) used one extra modulus per private point of an old period. It gave an additive variational formula with no linear bound on the size of the new system.

## Refining the distinguished class

Put $a=v_2(L)$ and $A=D\setminus\{n\}$. For an assignment on $A$ denote by $H$ the holes modulo $L$. Call the assignment admissible when $H$ lies in one class modulo $n$. There is at least one admissible assignment. Every assignment has at least one hole. For any subset of $A$ an assignment with holes in one $n$-class forces that subset to be all of $A$, because putting back a single $n$-row covers every integer.

The odd part of $n$ is greater than one. If $a=0$ this follows from $n>1$. Otherwise, the rows below the highest binary digit form a proper subset. Over one of their holes both top binary values must be covered, so at least two distinct moduli carry $2^a$. The largest of them has an odd factor.

For now allow repeated auxiliary moduli. A list of tests succeeds if their classes can cover $H$ for **some** admissible assignment. The empty list fails, and a single test of modulus $n$ succeeds. Choose any prime-factor chain
$$
                      n=m_0\mid m_1\mid\cdots\mid m_s=L,
                   \qquad m_i/m_{i-1}=q_i\text{ prime}.
$$
Maintain a frozen list $F$ and one distinguished test $m_{i-1}$ such that $F$ fails and $F$ together with that test succeeds. At step $i$ replace the distinguished test by the least number $t_i$ of identical $m_i$ tests for success together with $F$. All frozen residues and the old assignment are allowed to change in this minimum. We have $1\le t_i\le q_i$: the $q_i$ children partition a successful parent class. Freeze $t_i-1$ of the new tests, leaving the last distinguished. Minimality gives the induction invariant. At the end the distinguished test is $L$ and its deletion prevents success. Delete redundant frozen tests one by one while preserving success. The remaining multiset $T$ is minimal for success under all reassignments, has a distinguished test $L$, and has size
$$
                            h\le 1+\sum_i(q_i-1)=1+B(L/n).
$$
This remains true when $s=0$. The count depends on the prime digits to refine, independently of the number of private residues in the distinguished class.

## Implementing the tests with distinct integer moduli

Write $T=(m'_1,\ldots,m'_h)$ with $m'_h=L$ and put $t=h+2$. Retain $A$. Add one row for each new binary digit $1\le j\le t$: at $j=1$ use $2n$, and at $2\le j\le t$ use $2^{a+j}$. Also add the $h$ moduli $2^{i+2}m'_i$ for $1\le i\le h$. Every $m'_i$ divides $L$ and is a multiple of $n$, hence has binary valuation $a$ and an odd factor. Binary levels separate different tests, distinguish all new rows from old ones and distinguish a test from the power of two at its own level. The period is $2^tL$ and the last test has exactly that modulus.

Take a successful assignment for $T$. In the $t$ new bits, the first-type row at level $j$ covers the pattern whose first one is at $j$, using the common low $a$ binary bits of the old holes. At the first level the row $2n$ also imposes their common $n$-class. For a test row use its chosen old class and set its initial $i+2$ new bits to zero. Only tests meeting old holes are needed, and their old bits agree with the common low bits. These residue specifications are compatible modulo each row, by the Chinese remainder theorem. Every lift of every old hole is covered.

Consider any covering assignment on any subset. Over a hole of the retained old rows, the fraction a level-$j$ row can cover is at most $2^{-j}$. The first-type rows together serve at most $1-2^{-t}$. If the first row is absent or its $n$-class misses an old hole, this budget loses another $1/2$, whereas even all the test rows together serve at most $\sum_{j=3}^t2^{-j}<1/4$. Thus the first row is present and all old holes are in its $n$-class. This forces every row of $A$ to be present and the old assignment to be admissible. Each hole must belong to some test's old projection since the first type alone is insufficient. Minimality of $T$ now forces every test to be present.

In particular there is an old hole outside all the projections of the first $h-1$ tests in this assignment: otherwise these tests would succeed by themselves. Above this hole the last test supplies at most $2^{-t}$. The full budget $1-2^{-t}$ of the first type is required, so every first-type row is present as well. This proves irreducibility for arbitrary reassignment. The size is $k+2h+1$. Use the Znám–Simpson bound $B(L)\le k-1$ to get the stated uniform bound. The retained old rows already give the asserted reciprocal sum.

For exact padding, if the full period is $P$ replace its row by $2^{v_2(P)+1}$ and $2P$. These have the new top binary digit and their projections have a common intersection of modulus $P$ whenever it is nonempty. A hole of the ordinary rows needs both top sections, hence both new rows, and contracting recovers an old covering assignment. Conversely the two rows can fill the lifts of the old distinguished class. Their mass is at least $1/P$, the size increases by one and $2P$ belongs to the new set. Iterate. In particular $R_*(3k+1)\ge R(k)-1/2$ and $R_*(K)\ge R(\lfloor(K-1)/3\rfloor)-1/2$ for sufficiently large $K$. Together with $R_*(k)\le R(k)$ and $\log(3k+1)\sim\log k$ these prove both assertions about leading coefficients.

## Persistence of a reciprocal surplus at later sizes

There is a stronger additive comparison. As $k$ and $u=K-3k-1$ both tend to infinity,
$$
                 R_*(K)\ \ge\ R(k)-R_0(k)+R_0(u)-o(1).
$$
In particular if $K/k\to\infty$, the excess $R(k)-R_0(k)$ persists at the later size $K$ up to $o(1)$ above its own baseline $R_0(K)$. The statement is uniform in the input covers.

Put $\Phi(L)=\sum_{p^j\mid L}H_{p-1}/p^j$, over positive prime-power positions. Our first-type binary rows have total mass $\Phi(2^tL)-\Phi(L)-(2^{-a}-1/n)/2$. Removing the full-period test and keeping the nonnegative mass of all other tests gives
$$
 S(E)-1/(2^tL)-\Phi(2^tL)
    \ge S(D)-\Phi(L)-\tfrac12(2^{-a}+1/n)
    \ge S(D)-R_0(k)-o(1).
$$
The last inequality uses $1/n\le2^{-a}$ and the uniform harmonic knapsack bound $\Phi(L)+2^{-a}\le R_0(k)+o(1)$ from the [preceding proof](unrestricted-transfer.md).

Take the largest integer $y$ with $B(\operatorname{lcm}(1,\ldots,y))\le u$. Starting at $E$, install only the missing prime powers $p^j\le y$ in increasing prime order and increasing exponent at each prime. At each such position, of old period $P$, replace the terminal by $dp^j$ for $1\le d<p$ and a new terminal $pP$. All of $1,\ldots,p-1$ divide $P$ at this step since their prime powers have already been installed or were present initially. Distinctness at the new position follows as in the [ordinary extension proof](transfer.md): the old $p$-free part exceeds $p-1$ since it contains $\operatorname{lcm}(1,\ldots,p-1)$ for $p\ge5$, contains 4 for $p=3$, and has an odd factor for $p=2$. The residue assignment fills all but one new lift of the old hole with the $p-1$ side rows. After any deletion of an old ordinary row the others leave at least two old holes under every assignment, since one old singleton cannot finish a proper cover. Each old hole needs at least one lift beyond the side rows, whereas the new terminal serves at most one such lift overall. Thus old rows are indispensable, and loss of any new row leaves a hole. These extensions preserve the ordinary sum minus $\Phi$ exactly. They cost at most $u$ rows even when the initial period contains very large prime powers. Padding by ordinary binary extensions preserves the same difference.

The final period includes every prime power through $y$, so its $\Phi$ is at least $\sum_{p^j\le y}H_{p-1}/p^j=R_0(u)+o(1)$ by the [earlier zero-defect estimate](anchored.pdf). This proves the additive comparison. When $K/k\to\infty$, $u/K\to1$, so the same estimate by partial summation gives $R_0(u)=R_0(K)+o(1)$.

## Checks and limits of the refinement method

On a full fibre of size $d=L/n$, the abstract bound $1+B(d)$ is sharp for a minimal successful list containing a required point test. In a covering assignment, at the distinguished point every other test misses. Change just one prime digit of that point at a time to each possible alternative. Any test missing the distinguished point can hit at most one of these $B(d)$ alternatives: a tested digit where its residue disagrees has to be the changed digit and value. Thus at least $B(d)$ other tests are needed. The successive partition into prime children attains the bound. This sharpness statement concerns the auxiliary fibre model.

For a concrete example with several private residues, take the earlier 15-row system of period 420 and distinguish 20 (it also has full binary valuation and odd part greater than one, the only two conditions on $n$ used in the construction). The [earlier proof](unrestricted-transfer.md) exhibits holes $40,100,160,340$. In every admissible assignment at least four different residues modulo 140 occur among the holes. Indeed the lower rows have two holes with the same residue modulo 12 and different residues modulo 5. One lies outside the distinguished 20-class. All seven rows divisible by 7 must serve its seven lifts in distinct sections, so the four of these rows with 5 in the cofactor miss the other hole in four distinct sections. Those sections are distinct modulo 7 and hence modulo 140. It follows that the three tests of modulus 140 and one of modulus 420 used by the checker suffice, and no three of these tests can succeed under reassignment. The resulting set has 24 rows and full period 26,880.

The [exact checker](linear-full-period-check.py) independently tests success and every deletion in 33,529 finite hole-family and refinement-chain cases. In a second test, the actual integer system $\{2,3,4,5,6,10,15,20,30\}$ has period 60. The lift retaining all but 20 has 12 distinct moduli and full period 480. Direct enumeration with digit-permutation symmetry verifies that all nine source deletions and all twelve lifted deletions fail under arbitrary reassignment. The 24-row example has a direct full-period coverage check and the written deletion argument above. The general proof is written and awaits independent review. The earlier $\Theta(\log k)$ result is credited to Star Fleet Math and Wouter van Doorn, formalized by dk8827. Öztürk's coefficient bounds and the original Erdős–Graham questions are discussed in the [companion paper](../reciprocal-sums/). The unresolved step is a sharp upper bound for systems with a required singleton modulo their full period, or a construction in that class with a larger leading coefficient.
