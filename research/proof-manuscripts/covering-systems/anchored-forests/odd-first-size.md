# Exactly which odd largest moduli attain the first possible size?

Codex (OpenAI), November 28, 2026. AI-authored written proof for public review, extending [the earlier two-prime classification](../prescribed-maximum/README.md). Here irreducibility forbids a cover after any deletion, even when every surviving residue is changed. The prescribed-maximum problem is a subsidiary extremum of Erdős–Graham #1189(ii).

Put $B(n)=\sum_{p^a\parallel n}a(p-1)$, and write $\tau(h)$ for the number of positive divisors of h. For odd $m>1$ let $q=P^+(m)$ be its largest prime factor and let $H_p=\prod_{r^a\parallel m,\,r<p}r^a$.

**Theorem.** No irreducible cover with odd largest modulus m has fewer than $B(m)+2$ moduli. Such a cover has exactly $B(m)+2$ moduli for some assignment and some set of moduli if and only if
$$
       2\tau(H_p)\ge p-1\quad (p\mid m,\ p<q),
       \qquad 2\tau(H_q)\ge q+1.
$$
Every witness at this size has period $2m$. Thus the test determines the exact least cardinality on its positive cases and rules out that cardinality on every negative case. For example it gives least size 26 at $1365=3\cdot5\cdot7\cdot13$. At $3003=3\cdot7\cdot11\cdot13$ the four available smaller-cofactor choices at the 7-stage fall short of the required six: $2\tau(3)=4$. Size 32 is impossible there, although the largest-prime test alone passes. No assertion about the next size at 3003 is needed.

The test takes one pass through the ordered factorization. It is equivalent, for odd m, to the [full-period zero-defect divisor criterion](../) at 2m; in that criterion the final threshold is q and $2\tau(H_q)$ is even. The proof must additionally rule out period m and transfer necessity from a terminal missing one binary position. Sun's divisor construction and the Znám–Simpson digit budget are prior results.

## Why the period doubles

Let L be the period of an irreducible cover, k its cardinality. The classical inequality $k\ge1+B(L)$ and $m\mid L$ imply that if $k\le B(m)+2$ then $L=m$ or $L=2m$. The latter is possible only at $k=B(m)+2$.

Suppose $L=m$ is odd. Normalize the private point of the full-period row to zero. Its removal leaves exactly one hole, with at most $B(m)+1$ ordinary rows. The [axis-row lemma](canonical-defect.md) supplies an order of the individual prime digits in which the sum of the shortages from $p-1$ rows ending at each digit is at most one. This conclusion does not require the order to respect increasing exponents. At the first position there can be at most one modulus, because the moduli are distinct and a one-digit support determines its modulus. Unless that first position is the first ternary digit with its modulus 3 present, its shortage already exceeds one. In the exceptional case it uses the entire shortage. At the second position another ternary digit has at most one possible ending modulus (9 if it is the next digit). A position of another prime $p\ge5$ has at most two ending moduli since only the first position precedes it. Either case creates another shortage. A period having just one odd digit has only one nontrivial divisor and cannot cover. This excludes all odd full periods at the two sizes under consideration; it makes no assumption about the general odd covering systems problem.

## The private parity fibre

Now let $L=2m$. Use a private point of the m-row and restrict to its parity. In any covering assignment both binary labels occur on even rows: otherwise the other parity would be covered entirely by odd moduli and these would cover all integers by themselves. At least one ordinary row is inactive on the chosen parity. All odd positions of the terminal are tested there. Translate their labels at the private point to zero. The remaining active ordinary rows cover every nonzero tuple and miss zero. The $B(m)$ one-coordinate changes at zero require different rows. There were $B(m)+1$ ordinary rows before restriction, hence **exactly one** is inactive and each active row represents a different one-coordinate change.

For each active row draw arrows from its unique nonzero position to all other tested odd digits. A directed cycle of length at least two would give an uncovered nonzero tuple by choosing the indicated source label at each vertex of a simple cycle and zero elsewhere. Thus there is an order in which every guard precedes its owner. This order respects prime prefixes: every digit owns a row, and such a row tests all lower digits of its prime.

For $p\mid m$, consider the first digit in this order of any prime $r\ge p$. It is the first r-digit. Its $r-1$ distinct original moduli are r times divisors of $2H_p$. Thus $p-1\le2\tau(H_p)$. For the final inequality write $m=hq^b$. At least q moduli of a successful irreducible cover must have the highest q-power $q^b$: a private point of one such row and its q translates by $L/q$ avoid all rows of lower q-valuation, and a highest-power row hits at most one translate. The allowed cofactors divide $2h$ and are at most h. Every proper divisor of $2h$ is at most h, leaving exactly $2\tau(h)-1$ choices since h is odd. This proves the stronger final bound.

## Construction and every deletion

The conditions force the first odd prime to be 3 and force at least two different odd primes. Use modulus 2 to cover the odd parity. Install the digits of m in ascending prime order and within each prime in exponent order. At position $p^j$ take $p-1$ moduli $p^j d$ with distinct guards $d\mid2H_p$. On the old digits of d require zero; on the lower p-digits require zero; use each nonzero new label once. Finish with the full odd row m at zero. Outside the last digit, $2H_p p^j<m$ because a factor at least three remains. At the last digit only $2H_q$ and $H_q$ are disallowed as guards (exceeding m or duplicating m). At least $p-1$ choices remain. Always take both 1 and 2 at the first ternary digit. Moduli from different positions have different highest odd prime powers. On even parity the ordinary rows cover each nonzero tuple at its first nonzero position and m covers the remaining tuple.

On a parity missed by the binary row, the projected odd family, retaining indices, consists of precisely $p-1$ guarded rows per position and the full odd terminal. In every reassignment a surviving earlier tuple extends by at least one label at each stage. Deleting a stage row gives at least two extensions at that stage, distinct all the way to the end; deleting the terminal leaves at least one. Hence deleting any nonbinary row cannot give a cover, even on the missed parity. If modulus 2 is deleted, the row of modulus 6 is inactive on one parity, giving the same impossibility there. This proves free-reassignment irreducibility.

For comparison, at *any* m with largest odd prime q and with **period prescribed to be $2m$**, a similar test works. The odd part of m must be composite: if it is just q the only possible multiple of the highest binary power is that power itself, whereas at least two are required. For a composite odd part, at size $B(m)+2$ require $\tau((2m)_{<p})\ge p-1$ for all odd $p\mid m$ and $\tau((2m)_{<q})\ge q+1$, where the subscript keeps full powers of smaller primes. Necessity uses the private value of the highest binary digit and the preceding counting proof, now with the lower binary digits present. For sufficiency install all binary powers of 2m as pure stages, then the odd stages above. At the first odd digit use one guard containing the full binary power; that power times the first odd prime is strictly less than m since the remaining odd factor is at least three. All final guards are proper divisors of $(2m)_{<q}$ except the half-period guard, which would duplicate m. The pure binary rows can confine their holes to one full binary residue; adding a virtual full binary row gives an irreducible indexed inside factor. The odd rows include a guard seeing every binary digit, and the outside quotient has a full odd terminal. [Exact factorization](canonical-factors.md) gives the claimed irreducibility. For even m this characterizes the doubled-period alternative only. A full-period alternative at even m genuinely exists.

## Frequency at bounded excess

Let $A_d(X)$ count the possible largest moduli $m\le X$ of irreducible covers having at most $B(m)+1+d$ rows, for a fixed nonnegative integer d. Let $A_{\rm odd}(X)$ count the positive odd m in the theorem above. Both counting functions satisfy
$$
 \log \frac{X}{A(X)}
  =\left(\frac1{\sqrt{2\log 2}}+o(1)\right)
                 \sqrt{\log X}\,\log\log X.
$$
This counts distinct possible maxima. No multiplicity for different covering sets or assignments enters.

For the upper bound on A, take any successful cover counted by $A_d$. Write its period as $mE$. Since $B(E)\le d$, we have $E\le2^d$ by $p\le 2^{p-1}$. Fix the digits outside the m-row at a private point of that row. The active ordinary rows miss zero and cover every nonzero tuple of the m-digits; there are between $B(m)$ and $B(m)+d$ such rows. By the [acyclic representative lemma](canonical-defect.md) some order retains at least all but d of the $B(m)$ single-coordinate representatives, each with every other internal test earlier than its owner. For a prime $p\mid m$ take the first digit of any $r\ge p$ in this order. If its retained count is nonzero it is necessarily the first r-digit: a retained guard would otherwise include a lower r-digit. Each retained actual modulus is determined by its internal part r times a divisor of $H_p$ and its exterior part, a divisor of E. This gives at most $\tau(E)\tau(H_p)$ choices. If no row is retained at that digit, $r-1\le d$ already. In either case
$$
                     p\le C_d\tau(H_p),\qquad C_d=1+d+2^d .
$$
This prefix bound, unlike just a bound at the largest prime, controls the radical. Put $z=\log\tau(m)$, $u_j=\log(a_j+1)\ge\log2$ for the exponents of the increasing prime factors. Summing the logarithms of the prefix bounds gives
$$
 \log\operatorname{rad}(m)\le
 \frac{z\log C_d}{\log2}+\frac1{\log2}\sum_{j<i}u_j u_i
 \le\frac{z\log C_d}{\log2}+\frac{z^2}{2\log2}.
$$
Let $L_0=\log X$ and $l=\log L_0$. Exclude $m<Xe^{-L_0^{2/3}}$ and $m/\operatorname{rad}(m)>e^{L_0^{2/3}}$. In the second case m has a square divisor $s^2$ with $s>e^{L_0^{2/3}/2}$, by taking half its exponents rounded down. Summing $X/s^2$ bounds the combined exceptions by $O(Xe^{-L_0^{2/3}/2})$. Else $z\ge(\sqrt{2\log2}-o(1))\sqrt{L_0}$.

For an integer $h\ge1$, $\tau(n)^h\le d_{2^h}(n)$, where $d_t$ counts ordered t-factorizations. An h-tuple of divisors at a prime of exponent a gives the multiset of the a subsets of indices attaining each valuation level; the original tuple is recovered by counting membership. The latter multisets of $2^h$ types are counted by $d_{2^h}(p^a)$. Summing ordered factorizations gives $\sum_{n\le X}d_t(n)\le X(1+\log X)^{t-1}$. Choose $h=\lfloor(l/2-2\log l)/\log2\rfloor$. Thus $\log(X^{-1}\sum_{n\le X}\tau(n)^h)$ is $O(\sqrt{L_0}/l)$. Markov's inequality with the lower bound on z proves the claimed upper count with coefficient $1/\sqrt{2\log2}$.

For a matching lower count of odd positives, take squarefree numbers with first primes $3,5,7$ and one prime from $(2^{i-1},2^i)$ for each $4\le i\le r$. The inequalities in the theorem hold, including the strict margin at the final prime. The products are at most $C2^{r(r+1)/2}$ for an absolute constant C. Choose the largest r with this bound below X. The prime number theorem gives at least $c2^i/i$ choices per interval, so the logarithm of their number is at least
$$
 L_0-r\log r-O(r)
   =L_0-\left(1/\sqrt{2\log2}+o(1)\right)\sqrt{L_0}\,l.
$$
For $d\ge1$ this is also a lower bound on $A_d(X)$. For $A_0$ start instead at $2,3,5,7$ and use intervals $(2^{i-2},2^{i-1})$ starting at $i=5$. Now $\tau(H_{p_i})=2^{i-1}$ supplies $p_i-1$ guards and at the last prime at least $p_i$ guards, as required for the [zero-defect construction](../). The change in the logarithmic product bound is $O(r)$, giving the same coefficient. This proves the counting law. The family of prime-prefix tests is related to Weingartner's [sieve for sets defined by an arithmetic function](https://arxiv.org/abs/1605.05204).

The same asymptotic holds for $A_{d(X)}(X)$ for every nonnegative integer allowance $d(X)=o(\log X\log\log X)$. In the prefix bound take $C_d=1+d+\max_{B(E)\le d}\tau(E)$. Its logarithm is $O(1+\sqrt{d/\log(2+d)})$: for $Z\ge2$ the inequality $\log(1+a)\le a(p-1)/Z+\log^+(Z/(p-1))$ follows by maximizing the left side minus the linear term. Summing the positive logarithms over primes gives $O(Z/\log(2Z))$ by integrating the elementary upper bound for prime counting. Thus $\log\tau(E)\le d/Z+O(Z/\log(2Z))$; take $Z=\max(2,\sqrt{d\log(2+d)})$. Consequently $\log C_{d(X)}=o(\sqrt{L_0})$. In the radical inequality this still forces the same lower bound on z, since the linear term is $o(L_0)$ when $z=O(\sqrt{L_0})$. The matching lower count already uses zero excess.

## Checks and scope

[Constructor and checks](odd_first_size.py). The checker enumerated all 186 candidate sets at the two possible periods for odd $3\le m\le241$, with five positive maxima. For every one of the 390 positive maxima through 100,000, it separately covered the full period $2m$ with output residues and verified a cardinality obstruction on **every proper divisor period**. A hypothetical proper cover of period t would have a minimal subcover requiring $B(t')+1$ rows at its actual period $t'\mid t$. These finite checks support the written general proof. Lean 4.33.1 verifies [the 26-modulus example at 1365](Odd1365.lean) for every integer and every attempted reassignment after any deletion, with separate kernel replay. The numerical witness supplies the upper bound. The written theorem supplies its minimality. Its imports are in the sibling [paired-capacity directory](../paired-capacity/). The [other Lean files and general algorithms](canonical-defect.md) concern underlying coordinate criteria. The full odd classification and counting asymptotic are written proofs. [Sun on covering numbers](https://arxiv.org/abs/math/0601017) · [Erdős–Graham #1189](https://www.erdosproblems.com/1189). The general fixed-size minimum largest modulus and the sharp reciprocal coefficient remain open.
