# Which integers occur as the largest modulus of an irreducible cover?

An irreducible covering set is a finite set of distinct integers greater than one for which some choice of one residue per modulus covers the integers, while every proper subset fails for every choice of residues. Write \(\kappa(m)\) for the least cardinality of such a set with largest member \(m\), and set it to infinity if none exists.

**Theorem 1.** Let \(m>1\), let \(q\) be its largest prime divisor, and write \(m=hq^b\) with \(q\nmid h\). Then \(\kappa(m)<\infty\) if and only if \(h>q\). The integers passing this test have natural density \(1-\log 2\).

The theorem decides the union of the sets of possible largest moduli over all cardinalities in Erdős #1189(ii). The catalog asks for the extremes at each prescribed cardinality. Sections 3 and 4 below also give exact minimum cardinalities for several infinite families.

## 1. The necessary inequality

Write \(L\) for the least common multiple of the moduli in any irreducible cover. Take a prime \(p\mid L\) and let \(p^B\parallel L\). At least \(p\) moduli are divisible by \(p^B\). To see this, fix a covering assignment and choose a class whose modulus has the full \(p\)-power. It contains a private point \(x\bmod L\), since deleting the class would otherwise leave a cover. Consider the \(p\) points \(x+jL/p\), \(0\le j<p\), modulo \(L\). Every modulus with smaller \(p\)-exponent divides \(L/p\). Its class misses \(x\) and hence misses the entire list. Each remaining class hits at most one point in the list, since the \(p\) points have distinct residues modulo \(p^B\). This proves the claim. This prime-power multiplicity argument is classical and appears in the proof of Sun's Lemma 2.1.

Distinct positive multiples of \(p^B\) all at most \(m\) can number at most \(\lfloor m/p^B\rfloor\). Take \(p=q\). As \(B\ge b\), we get \(h=m/q^b\ge q\). Coprimality excludes equality.

## 2. A construction with controlled maximum

Let \(f(n)=\sum_{p^a\parallel n}a(p-1)\). We use the Znám–Simpson bound in its LCM form: an irredundant covering assignment of period \(L\), where \(L\) is the LCM of its moduli, has at least \(1+f(L)\) classes.

Suppose \(h>q\). Set
\[
  W=\operatorname{lcm}(h,1,2,\ldots,q-1),\qquad L=Wq^b .
\]
All primes dividing \(W\) are smaller than \(q\). Each maximal prime power in \(W\) is at most \(h\). Read the prime-power coordinates of an integer modulo \(L\) in increasing prime order, reading the base-\(p\) digits in each coordinate from least to most significant. The following assignment uses one class per nonzero digit value at each stage, with one additional class for zero at the final stage. This adapts the divisor construction of Sun, Theorem 1.1.

At digit \(j\) of a prime \(p\mid W\), use a separate modulus \(d p^j\) for each nonzero digit value \(t\), with \(d=t\) for \(1\le t<p\). In this assignment the class is zero modulo \(d\) and is \(t p^{j-1}\) modulo \(p^j\). These congruences are compatible since \(d<p\), and \(d\) divides the product of the earlier prime-power coordinates. The last assertion holds because \(d<q\), \(d\mid W\), and all of its prime factors are smaller than \(p\). Each modulus is at most \(h(p-1)<m\).

At the nonfinal \(q\)-digits use the same rule with multipliers \(1,\ldots,q-1\). At the last digit use the \(q\) distinct multipliers in \(D=\{1,\ldots,q-1,h\}\), assigning all \(q\) digit values bijectively to them. Again each class is zero on its multiplier and fixes the \(q\)-coordinate to the assigned digit times \(q^{b-1}\) modulo \(q^b\). Every modulus is at most \(m\), and \(hq^b=m\) occurs. The largest prime and its exponent distinguish moduli at different stages. At a single stage, multipliers distinguish them.

To see coverage, take the first nonzero digit. All earlier coordinates and all lower digits of its prime are zero, so its assigned class covers the point. If the earlier digits are all zero up to the final stage, its \(q\) classes cover every final value, including zero.

For irreducibility, consider any new residue assignment on any covering subset. Delete redundant classes to get an irredundant subsystem of LCM \(E\mid L\). At most \(p-1\) moduli per digit of \(p\mid E\) can divide \(E\), except for the final \(q\)-digit, which has \(q\) moduli available when \(q^b\mid E\). All \(q\) final moduli together have LCM \(q^b\operatorname{lcm}(D)=L\). Thus for every proper divisor \(E\) at most \(f(E)\) of the moduli divide \(E\), which contradicts the LCM bound. If \(E=L\), the bound requires every one of the \(1+f(L)\) moduli. This proves Theorem 1's criterion and gives an explicit constructor.

**Density.** Each excluded \(m>1\) has a unique expression \(ip^j\) with \(p\) prime, \(j\ge1\), \(1\le i<p\). The prime is automatically the largest factor. Hence the exact excluded count through \(X\), omitting 1, is
\[
   \sum_{p^j\le X}\min(p-1,\lfloor X/p^j\rfloor).
\]
For \(j\ge2,\ p\le X^{1/3}\), the contribution is \(O(X^{2/3}\log X)\) by counting the exponents and summing \(p\). For larger \(p\) only \(j=2\) can occur and the contribution is \(O(X\sum_{n>X^{1/3}}n^{-2})=O(X^{2/3})\). For \(j=1,\ p\le\sqrt X\) the bound is \(O(X/\log X)\) by the standard prime-counting upper bound. For \(p>\sqrt X\) the sum is \(X\sum_{\sqrt X<p\le X}1/p+O(\pi(X))\). Mertens' reciprocal-prime estimate gives \(\log 2+o(1)\) for the prime sum. This proves the claimed density.

## 3. A lower bound on cardinality and sharp instances

With \(q,h,b\) as above, put
\[
 C(h,q)=\min\{f(V):h\mid V,\ (q,V)=1,\ \#\{d\mid V:d\le h\}\ge q\}.
\]
The minimum of the empty set is infinity. In a cover of LCM \(q^B V\) with \(q\nmid V\), the top digit requires \(q\) classes. Dividing their moduli by \(q^B\) gives \(q\) distinct divisors of \(V\) at most \(m/q^B\le h\). Also \(h\mid V\). Consequently
\[
 \kappa(hq^b)\ \ge\ 1+b(q-1)+C(h,q).
\]
This minimum is an effective finite calculation. Replace \(V\) by its gcd with the LCM of all \(q\)-coprime integers at most \(h\). This retains \(h\) and every tested divisor of \(V\), and can only lower the cost.

Here are fourteen cases of equality, valid for **every** \(b\ge1\). The minimum cardinality is \(1+b(q-1)+C\).

| \(h\) | \(q\) | minimizing \(V\) | \(C\) |
|---:|---:|---:|---:|
|9|5|18|5|
|9|7|72|7|
|25|11|300|12|
|25|13|600|13|
|25|17|8400|20|
|25|19|25200|22|
|25|23|61261200|60|
|27|5|54|7|
|27|7|54|7|
|27|11|216|9|
|27|13|540|12|
|27|17|10800|18|
|27|19|15120|20|
|27|23|2162160|42|

The entries use finite exhaustive calculations supplied in the code. For each \(V\) in the table take the smallest \(q-1\) divisors of \(V\) and \(h\) as the final multipliers. These \(q\) numbers are distinct, at most \(h\), and their LCM is \(V\). At every earlier prime \(p\mid V\) and level \(j\), take the smallest \(p-1\) divisors of the earlier prime-power product. The checker verifies that after multiplication by \(p^j\) these are at most \(hq\), already at \(b=1\). The earlier \(q\)-levels can reuse the first \(q-1\) final multipliers. The coverage and arbitrary-reassignment arguments in section 2 apply for every \(b\).

For the earlier unresolved test \(m=315=45\cdot7\), only six divisors of \(h=45\) are available, giving \(C(45,7)\ge f(45)+1=9\). The choice \(V=90\) supplies the construction at equality. Thus \(\kappa(315)=16\). For \(75=3\cdot5^2\), the criterion gives \(\kappa(75)=\infty\). In particular the earlier solver timeouts on the two inputs concealed different outcomes.

**A strict gap in the lower bound.** For \(m=175=25\cdot7\), one has \(C(25,7)=10\) but \(\kappa(175)=18\). Indeed \(V=25t\) of cost at most ten requires \(f(t)\le2\), so \(V\in\{25,50,75,100\}\). Only 100 has seven divisors at most 25. A putative 17-class cover therefore requires \(B=1\) and \(L=700\). There are just eight eligible nontrivial divisors of 100 and seven eligible divisors of 700 divisible by 7. This gives only fifteen distinct moduli. For 18 classes take \(V=150\). For the two levels of 5 use multipliers \(1,2,3,6\), after processing 2 and 3. At the last level of 7 use \(1,2,3,5,6,10,25\), with LCM 150. Section 2 gives the cover and irreducibility. This example disproves the proposed equality with the divisor-count lower bound in general.

## 4. Which odd maxima on at most two primes have defect one?

For a cover of size \(k\) with maximum \(m\), let the defect be \(k-1-f(m)\). Among odd maxima \(m>1\) with at most two distinct prime divisors, defect one is attainable exactly for
\[
                  m=3^a q^b,\qquad 5\le q\le 2a+1
\]
with \(q\) prime and \(a,b\ge1\). Its least size in these cases is \(2+2a+b(q-1)\).

For necessity, the LCM bound and \(m\mid L\) imply \(L=m\) or \(2m\) at defect one. Even using every nontrivial divisor of an odd \(m\) supported on at most two primes, the reciprocal sum is smaller than \(3\cdot5/(2\cdot4)-1<1\). This rules out \(L=m\) and also defect zero. A prime-power maximum fails Theorem 1. If \(m=p^a q^b,\ 5\le p<q\), choose a parity missed by the class modulo 2, choosing either if that modulus is absent. On this parity at most two classes have any particular odd part \(d>1\), and each covers at most \(1/d\) of that parity. Their total relative density is at most \(2((5/4)(7/6)-1)=11/12\). Hence \(p=3\). Among divisors of \(2\cdot3^a\) exactly \(2(a+1)-1\) are at most \(3^a\). The \(q\) top-level multipliers must come from these, proving necessity.

Conversely, take \(V=2\cdot3^a\). Use the earlier binary digit and all ternary digits as in section 2, with multipliers 1 and 2 at each ternary digit. Choose \(q\) distinct divisors of \(V\) at most \(3^a\) including \(3^a\) and 2. Their LCM is \(V\), so they serve as the final multipliers. The same proof gives the required size and maximum.

Sun's Theorem 1.4(ii) already gives the related three-prime *primitive covering number* threshold for \(2\cdot3^a q^b\). The assertions here prescribe a largest modulus, its number of classes, and irreducibility under reassignment.

## 5. Exact least size for maxima \(5^a q^b\) at defect three

**Theorem 2.** Let \(q>5\) be prime and \(a,b\ge1\). Every irreducible covering set with largest modulus \(5^aq^b\) has at least
\[
                        4+4a+b(q-1)
\]
classes. This number is attained **if and only if** \(q\le4a\). In particular \(\kappa(25\cdot7^b)=12+6b\) for every \(b\ge1\).

We first establish an obstruction that permits arbitrary residue choices, even if every nontrivial divisor is available. For any primes \(5\le p<q\) and positive \(a,b\), the divisors greater than one of \(4p^aq^b\) cannot cover the integers. Fix a residue modulo 4 missed by the classes of moduli 2 and 4, using any missed residue if either class is absent. Write \(S=1+p+\cdots+p^{a-1}\), so \(p^a\ge4S+1\). For each \(1\le i\le a\), at most three moduli with odd part \(p^i\) are available. Their classes can exclude at most \(3p^{a-i}\) residues modulo \(p^a\) over the chosen residue modulo 4. At least \(K\ge p^a-3S\ge S+1\) residues survive these exclusions, where \(K\) denotes the actual number of survivors.

Take the Cartesian product of these \(K\) rows with all \(q^b\) residues in the last coordinate. For each \(1\le j\le b\), at most three classes with odd part \(q^j\) can touch \(Kq^{b-j}\) points each. The at most three classes with odd part \(p^i q^j\) can each touch at most \(p^{a-i}q^{b-j}\) points. This bounds the total contribution at level \(j\) by \(3(K+S)q^{b-j}\). Since \(3(K+S)<6K\le(q-1)K\), summing the geometric progression leaves an uncovered point. At \(p=5,a=2,q=7\) we have \(S=6,\ K\ge7\), so even summing over infinitely many levels gives covered proportion at most \(3(1+6/7)/6=13/14\) on the surviving grid.

Now write \(m=5^aq^b\) and \(L=tm\). The LCM bound gives \(k\ge1+4a+b(q-1)+f(t)\). If \(f(t)\le2\), then \(t\) is one of \(1,2,3,4\). For \(t\mid4\) the preceding obstruction applies. For \(t=3\), even the sum of the reciprocals of all permitted nontrivial divisors is less than \((4/3)(5/4)(7/6)-1=17/18\). Hence \(f(t)\ge3\), proving the lower bound. At equality \(t=6\) or \(8\). There are exactly \(4a\) divisors of each of \(6\cdot5^a\) and \(8\cdot5^a\) at most \(5^a\). Indeed, for the \(5\)-exponents from zero to \(a-2\) all four multipliers are possible, at exponent \(a-1\) exactly three are possible, and at exponent \(a\) just one. Section 1 now requires \(q\le4a\).

Conversely, suppose \(q\le4a\) and use \(W=6\cdot5^a\). Process the digits of 2 and 3 with multipliers 1 at the binary digit and 1, 2 at the ternary digit. At every 5-digit use the four earlier multipliers \(1,2,3,6\). Their moduli stay below \(m\), since \(q\ge7\). From the \(4a\) divisors of \(W\) at most \(5^a\), choose \(q\) distinct final multipliers including \(2,3,5^a\); their LCM is \(W\). Use any \(q-1\) of them at each earlier \(q\)-digit. Section 2 gives coverage and irreducibility under all reassignments. The total size is \(1+f(Wq^b)=4+4a+b(q-1)\).

Sun's Theorem 1.4(iii) had already supplied primitive covering periods with factors \(2,3,5,q\), and others with factors \(2,5,q\). Jones and White give counterexamples to a general converse to Sun's sufficient condition. The proof above derives its lower bound directly for the prescribed maximum.

## Verification, sources, and open directions

Codex produced the argument and programs at Jordan Pollard's request. The general statements have written proofs. The Python constructor outputs an explicit residue assignment for a given \(m\), or certifies impossibility by Theorem 1. Running it without arguments checks the decisions through 500, the cardinality table by two exhaustive methods (enumerating candidate LCMs and adjoining possible divisors), and the 315 example. Of the 109 positive decisions through 500, 76 had periods at most 100,000 and were also scanned point by point. The other 33 received the divisor-budget checks. Lean 4.33.1 verifies all 630 residues and the proper-period budget of the 315 example by kernel reduction without axioms. It also checks the abstract injection count for a private-point fiber. The general CRT construction and its use of the LCM bound have written proofs. Priority and independent review remain open.

The accompanying Lean file \(\texttt{SurvivingFiber.lean}\) checks the surviving-row inequality, the geometric budget for arbitrary depth, and the finite-set conclusion that any grid satisfying the written incidence bounds has an uncovered point. The CRT incidence bounds and Theorem 2 as a whole have written proofs. The Python checks also verify the small-divisor counts for auxiliary factors 6 and 8 through \(a=12\) and construct the equality witnesses through \(a=8,\ b=3\).

The first construction with \(W=\operatorname{lcm}(h,1,\ldots,q-1)\) can use more classes than necessary. Section 3 gives a smaller candidate \(V\), but primes in its factorization may lack enough admissible earlier multipliers to support the construction. The table and section 5 together determine the minimum for every \(h=25\), every largest prime \(q>5\), and every \(b\ge1\), with impossibility for \(q>25\). A remaining question is to recognize when the divisor-count lower bound is sharp without constructing a cover, and whether sharpness can change with \(b\) at fixed \(h,q\). The original extrema at a prescribed cardinality are a separate optimization.

- [Formal Conjectures, Erdős #1189, especially part (ii)](https://google-deepmind.github.io/formal-conjectures/src/FormalConjectures/ErdosProblems/%C2%AB1189%C2%BB/)
- [Z.-W. Sun, *On covering numbers*, Theorem 1.1, Lemma 2.1, and Theorem 1.4](https://arxiv.org/pdf/math/0601017)
- [L. Jones and D. White, *On primitive covering numbers*, especially Theorem 4](https://www.academia.edu/65929846/On_Primitive_Covering_Numbers)
- [P. Balister, B. Bollobás, R. Morris, J. Sahasrabudhe, M. Tiba, *The structure and number of Erdős covering systems*, Theorem 2.4 and Appendix A](https://arxiv.org/abs/1904.04806)
- [E. Öztürk, *Irreducible covering systems: the largest modulus, the maximal reciprocal sum, and exact values for at most nineteen moduli*, 2026 preprint](https://doi.org/10.13140/RG.2.2.16138.63684)
