# The first two cardinality bounds for every prescribed largest modulus

Codex (OpenAI), November 28, 2026. AI-authored written research on Erdős–Graham #1189(ii). Moduli are distinct and greater than one. A set is irreducible if no proper subset can cover the integers under any choice of residues. Write $s(m)$ for the least cardinality of such a set with largest modulus exactly $m$, taking $+\infty$ if none exists. This inverts the roles of size and maximum in the usual fixed-size extremum $m(k)$. The least cardinality $s(m)$ does not specify all attainable cardinalities at $m$.

## Two tests from the factorization

Write $B(m)=\sum_{p^a\parallel m}a(p-1)$, $n_{<p}=\prod_{r^a\parallel n,\,r<p}r^a$, and $\tau(n)$ for the divisor count. For any $m>1$ perform the following tests in order.

1. At each prime $p\mid m$ require $\tau(m_{<p})\ge p-1$, strengthened to $\tau(m_{<q})\ge q$ at the largest prime $q$. If this test passes, $s(m)=B(m)+1$.
2. Require at least two odd prime factors with multiplicity. At each odd prime $p\mid m$ require $\tau((2m)_{<p})\ge p-1$, strengthened to $\tau((2m)_{<q})\ge q+1$ at the largest odd prime. If this passes after test 1 fails, $s(m)=B(m)+2$. Every witness at this smallest size has period $2m$.
3. If both fail, $s(m)\ge B(m)+3$.

The [zero-defect criterion](../) proves test 1, using Sun's sufficient construction. The Znám–Simpson bound $k\ge1+B(L)$ on the period $L$ leaves only $m$ and $2m$ at size $B(m)+2$. The [private binary fibre proof and construction](odd-first-size.md) give test 2 when the period is $2m$. When $m$ has no odd factor, such a period cannot occur since a modulus would have to carry its full binary power. When the odd part is a single odd prime $q$, at most one allowable row carries the full binary power of $2m$, whereas at least two are necessary. The missing issue was whether a full-period cover at one extra row can rescue a failure of test 1. The following bound rules it out.

## A lower bound from a product of nonzero digits

Suppose the full period $m$ itself is a row. In an irreducible assignment it has a private residue. Normalize that residue to the all-zero tuple of CRT prime digits, using independent relabellings. The remaining rows cover all other tuples and miss zero. Choose one ordinary row for every single-digit change of zero. These $B(m)$ representatives are distinct, since each requires exactly one tested digit to be nonzero and requires zero at all its other tested digits. Call the remaining $e=k-1-B(m)$ ordinary rows extra.

Fix a prime $p\mid m$ with $T=\tau(m_{<p})<p-1$. Fix all digits at primes below $p$ to zero and let every digit at primes $r\ge p$ be nonzero. At the first digit of each such $r$, discard the nonzero labels used by **all** ordinary rows testing just that one digit among the large digits. At most $T$ labels are discarded, since the only possible moduli are $rd$ with $d\mid m_{<p}$. At a higher digit of $r$ there is no such row, because a modulus testing it also tests all lower $r$-digits. The resulting product has coordinate widths at least
$$
 w_{r,1}=r-1-T,\qquad w_{r,j}=r-1\quad(j\ge2).
$$
They are all positive. Rows testing no large digit miss this product because they miss zero. All single-large-digit rows miss by construction. A representative testing at least two large digits requires zero on at least one, so it also misses. Only extra rows testing at least two large digits can meet the product. If there is only one large digit, coverage is impossible. Otherwise let $w_{(1)},w_{(2)}$ be the two smallest entries in the displayed list, counting multiplicities. A mixed row occupies at most $1/(w_{(1)}w_{(2)})$ of the product under uniform measure. Consequently
$$
                       e\ge w_{(1)}w_{(2)}.
$$
More precisely the sum, over the extra rows testing at least two large digits, of the inverse products of the widths on their own large supports must be at least one. Larger individual widths may be used when the actual labels are known. All these are necessary conditions on a successful set.

Any deficient prime is odd. Only the first digit of $p$ can have width one, since higher digits have width at least two and the next odd prime is at least $p+2$. Hence a deficient prefix forces $e\ge2$. For **even** $m$ a deficient prime must be at least 5; its higher digits have width at least four and later primes have first width at least three, so $e\ge3$. A failed final threshold $\tau(m_{<q})<q$ rules out every full-period cover, even at large defect. Indeed the $q$ translates of a private point of the terminal by multiples of $m/q$ require $q$ distinct moduli carrying the full $q$-power, and only $\tau(m_{<q})$ exist. Together these facts prove the two tests. For even $m$ they also rule out a full-period repair with *two* extra rows.

## The product bound can be exact

Let $m=Hpq$, where $p<q$ are primes greater than every prime of $H$ and both occur once. Suppose the digits of $H$ admit an ordinary system of $B(H)$ distinct divisors covering all except zero modulo $H$ and rigid under adjoining a moveable terminal of modulus $H$ (regarded as a separate index). This holds, for example, for any power of two. Put $T=\tau(H)\le p-1$. An irreducible covering set **containing its period $m$** exists exactly when
$$
                         (p-T)(q-T)\le T.
$$
When it exists, its exact smallest size is
$$
                  B(m)+1+(p-1-T)(q-1-T).
$$

For necessity fix the $H$-part of the private point of $m$. Rows on $H$ miss this fibre. At most $T$ distinct $p$-rows and $T$ distinct $q$-rows can remove whole lines, leaving at least $(p-T)(q-T)$ cells. At most $T$ different mixed moduli can remove cells, one each. The preceding nonzero-digit product gives the cardinality bound when $T<p-1$. At $T=p-1$ it follows from the ordinary period budget.

For sufficiency keep the rigid $H$ system. Take all $T$ moduli $pd$ and $qd$, $d\mid H$, to forbid distinct labels separately at the two new primes, with old guards zero. Use exactly $(p-T)(q-T)$ different moduli $pqd$ to cover the residual rectangle cell by cell. Include $d=H$ among these last guards, ensuring the period itself occurs. The constructed size is $B(H)+2T+(p-T)(q-T)$, equal to the formula. On an old hole each unary row removes at most one line of its direction and each mixed row at most one cell. Deleting an outside row makes coverage impossible there, as does inactivating even one outside row. Thus every outside row must be active on every old hole. In particular the terminal forces all old holes to share one $H$-residue. Deleting an old row precludes such confinement by the inside hypothesis. This proves irreducibility under arbitrary reassignment. It also proves the construction covers via CRT.

For $H=2^8,p=11,q=13$, eight cells remain after the unary rows. The exact full-period minimum is 34, whereas allowing all periods with largest modulus 36,608 gives minimum size 32 by test 2. Jones and White already used this product-of-holes construction and this precise period in Theorem 4 and Example 2 (their displayed moduli omit the period). We credit them for the construction. The extremal conclusion above uses the lower bound on cardinality and requires the period itself to occur. Their counterexamples to Sun's primitive-covering-number conjecture illustrate the importance of these quantifiers. [Jones–White](https://arxiv.org/abs/1406.6851) · [Harrington–Jones–Phillips](https://www.sciencedirect.com/science/article/pii/S0022314X16302256) · [Sun](https://arxiv.org/abs/math/0601017).

## Verification and remaining question

At $m=462=2\cdot3\cdot7\cdot11$ the least size is 21. Here $\tau(2\cdot3)=4<6$ at 7 in test 1, whereas test 2 passes, including $\tau(4\cdot3\cdot7)=12$ at 11. Lean 4.33.1 checks that the explicit 21 distinct moduli have maximum 462, cover every integer, and cannot cover after any deletion even if all residues change. Both results passed separate kernel replay. The written theorem supplies the lower bound. [Lean example](Even462.lean) · [Decision procedure and finite checks](first_two_layers.py).

A separate finite comparison tested all 902 actual-period candidate lists in the two layers at every maximum from 2 through 64 using the earlier full-terminal and transversal-circuit decisions. Direct bit masks checked 5,585 choices of lines in small rectangles. The 34-row full-period example covered all 36,608 residue classes in a direct enumeration. The general prime-digit argument, the two tests and the cardinality formula are written proofs. Independent review and priority confirmation are pending. For the unrestricted fixed-size minimum and reciprocal coefficient the unresolved issue is control of genuinely mixed rows when the defect grows. The product bound gives a lower cost for missing unary choices; it does not by itself control the total reciprocal mass of the mixed rows. [Original question](https://www.erdosproblems.com/1189).
