# Erdős problem 420, part I

Let $D(n)=\tau(n!)$, where $\tau$ counts positive divisors. Use the natural logarithm. Part I asks whether, for every sufficiently large fixed real $C$,

$$
\frac{D(n+\lfloor(\log n)^C\rfloor)}{D(n)}\longrightarrow\infty.
$$

## The remaining arithmetic question

Does there exist a positive integer $A$ such that, for every sufficiently large integer $x$, there are a prime $p$ and a positive integer $s$ satisfying

$$
x < sp \le x+\lfloor(\log x)^A\rfloor,
\qquad s\le\lfloor(\log x)^A\rfloor?
$$

This question is equivalent to part I when the exponent is allowed to change. For large $x$, the displayed bounds also imply $s<p$, since $(\log x)^{2A}<x$. The formal condition in the accompanying Lean file allows $A=0$, which gives the same existence question by increasing $A$ to 1 if necessary.

## Why one hit per interval suffices

At a hit $m=sp$ with $s<p$, the exponent of $p$ in $(m-1)!$ is $s-1$. Indeed $m<p^2$, and the earlier multiples of $p$ are exactly $p,2p,\ldots,(s-1)p$. At $m!$ the exponent becomes $s$. The factor for $p$ in the divisor count therefore increases by $(s+1)/s$, and the contributions from every other prime are nondecreasing. Across any block containing that hit, the divisor count gains a factor of at least $1+1/s$.

Fix $C>2A$, put $L=\log n$, $h=\lfloor L^C\rfloor$, $b=\lfloor(2L)^A\rfloor$, and $t=\lfloor h/b\rfloor$. Divide the first $tb$ integers after $n$ into $t$ disjoint blocks of length $b$. For large $n$, each block starts at some $x$ with $n\le x\le 2n$, so $\log x\le 2L$. The arithmetic hypothesis supplies a hit within that block with $s\le b$. Multiplying the gains gives

$$
\frac{D(n+h)}{D(n)}\ge (1+1/b)^t\ge 1+t/b.
$$

Since $h/b^2\to\infty$, also $t/b\to\infty$. The Lean proof uses the sufficient threshold $C\ge2A+1$ and performs the accumulation in integer arithmetic. Its theorem **of_prime_multiples** takes just the uniform arithmetic assertion as a hypothesis.

## Why the conjecture also implies a hit

Fix a positive $C$ for which part I gives divergence, and put $h=\lfloor(\log n)^C\rfloor$. Write $P(m)$ for the largest prime divisor of $m$, $\Omega(m)$ for its number of prime factors with multiplicity, and $v_p$ for the exponent of $p$. For $m\ge2$, the divisor product formula and $\log(1+z)\le z$ for $z\ge0$ give

$$
\log\frac{D(m)}{D(m-1)}
\le \sum_{p\mid m}\frac{v_p(m)}{1+v_p((m-1)!)}
\le \frac{\Omega(m)P(m)}{m}.
$$

For the second inequality, $(m-1)!$ contains the multiples $p,2p,\ldots,(m/p-1)p$, so $1+v_p((m-1)!)\ge m/p$. Also $\Omega(m)\le \log m/\log 2$.

Suppose every $m$ in $(n,n+h]$ has cofactor $m/P(m)>(\log n)^{C+2}$. For large $n$, summing the one-step bounds gives

$$
\log\frac{D(n+h)}{D(n)}
\le \frac{h\log(2n)}{(\log 2)(\log n)^{C+2}}.
$$

The right side tends to zero. Divergence makes the left side at least $\log 2$ for every sufficiently large $n$. Thus every such interval contains some $m$ with $m/P(m)\le(\log n)^{C+2}$. Take $p=P(m)$, $s=m/P(m)$, and any integer $A\ge C+2$. This reverse implication is supplied as a written proof.

## Growth for almost every starting integer

For a fixed real $C>2.1$, write $F_C(n)=D(n+\lfloor(\log n)^C\rfloor)/D(n)$. The following unconditional consequence concerns the actual factorial divisor counts. There are constants $c_C>0$ and $\delta>0$ such that, for all sufficiently large $X$,

$$
\log F_C(n)\ge c_C(\log X)^{C-2.1}
$$

for all but $O(X/(\log X)^\delta)$ integers $n\in[X,2X]$. Thus, for each fixed threshold $M$, the proportion of integers up to $X$ with $F_C(n)\le M$ tends to zero. Part I also requires control at the exceptional starts.

**The arithmetic input.** Theorem 1.1 of Matomäki and Teräväinen gives absolute constants $c_0,\delta>0$. Outside a set of $O(Y/(\log Y)^\delta)$ integer starts $x\le Y$, the interval $(x,x+(\log x)^{2.1}]$ contains at least $c_0(\log x)^{1.1}$ distinct products $qp$ of two primes with $q\le (\log x)^{1.1}$. The theorem also gives a lower bound on $q$ that we do not need. [Paper, Theorem 1.1](https://arxiv.org/pdf/2207.05038) · [Journal publication](https://doi.org/10.1090/tran/8869)

**Divisor gain in one block.** At a good, sufficiently large start $x$, let $R=(\log x)^{1.1}$. Each of the products lies above $x$, so $p>q$. At the integer $m=qp$ the $p$-factor in the divisor count rises from $q$ to $q+1$. Therefore $\log D(m)-\log D(m-1)\ge\log(1+1/q)\ge1/(2R)$. The products are distinct, so they contribute at distinct steps of the factorial. A good block increases $\log D$ by at least $c_0/2$.

**From one block to a longer window.** Take $h=\lfloor(\log X)^C\rfloor$, $b=\lceil(\log(3X))^{2.1}\rceil$ and $t=\lfloor h/b\rfloor$. For $X\le n\le2X$, use the $t$ disjoint blocks of length $b$ starting at $n+jb$ for $0\le j<t$. Every start is at most $3X$ and the blocks fit within the window defining $F_C(n)$. Let $E$ be the exceptional starts in $[X,3X]$. For each $j$, the map $n\mapsto n+jb$ is injective. Counting pairs $(n,j)$ whose block starts in $E$ gives at most $t|E|$ pairs. Hence at most $2|E|$ starting integers $n$ can have at least half their blocks exceptional. Every other $n$ gains at least $c_0t/4$ in $\log D$. Since $t\asymp (\log X)^{C-2.1}$, this proves the bound. The proportion statement follows by summing over dyadic ranges.

**What the exceptional starts would have to do.** There is a further way a start $x$ can succeed. Suppose that for some fixed $B>0$ there is an integer $1\le k\le(\log x)^B$ such that $u=\lfloor x/k\rfloor$ is a good start in Theorem 1.1. Take one prime product $qp\in(u,u+(\log u)^{2.1}]$. Then
$$
x<kqp\le x+(\log x)^{B+2.1},\qquad kq\le(\log x)^{B+1.1}.
$$
Indeed, $qp\ge u+1$ gives the strict lower endpoint. For large $x$, $p>kq$ follows from $kqp>x$ and $(kq)^2<x$. Thus it would suffice to show that some fixed $B$ gives such a good rescaling for **every** sufficiently large $x$. The larger integer exponent $A=\lceil B+2.1\rceil$ then works in the original reduction.

A cardinality bound alone cannot establish this last assertion. For fixed $B>0$, take $x_j=2^{2^j}$ and form a set containing all $\lfloor x_j/k\rfloor$ for $1\le k\le(\log x_j)^B$. That set has only $O_B((\log Y)^{B+1})$ elements up to $Y$. Indeed, any contributing $x_j$ satisfies $x_j\le(Y+1)(\log x_j)^B$, hence $\log x_j\le2\log(Y+1)$ for sufficiently large $j$. There are $O(\log\log Y)$ such indices, each contributing $O_B((\log Y)^B)$ elements. Nevertheless, all rescalings fail at each $x_j$ if this sparse set is declared exceptional. The unresolved implication requires arithmetic information about the actual exceptional set.

## Status and sources

The missing step is a proof or disproof of the uniform arithmetic assertion. Density along selected subsequences, as proved for parts II and III, answers a different quantifier in the problem. The fixed-exponent weighted-sum comparison in the working report below is a related approach. The argument here changes the exponent to turn a uniform single hit into growth.

- [Erdős problem 420](https://www.erdosproblems.com/420)
- [Erdős, Graham, Ivić and Pomerance, *On the number of divisors of n!*](https://math.dartmouth.edu/~carlp/factorial.pdf)
- [Plasma AI’s Lean proofs for parts II and III](https://github.com/plasma-ai/erdos-420)
- [Earlier fixed-exponent reduction to a weighted sum of prime multiples](https://erdosproblemaday.com/report/420)

## Formal verification of the finite counting bound

The Lean file below checks the pair-counting step for arbitrary finite sets of starts and exceptions. It was checked with Lean 4.33.1 and the project's pinned Mathlib. Its only axioms are `propext`, `Classical.choice`, and `Quot.sound`. The analytic theorem and its application above are given as a written proof.

```lean
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A finite exceptional-set estimate for disjoint short blocks of a long interval. -/
namespace DensityBlocks

def badBlocks (bad : Finset ℕ) (t b n : ℕ) : ℕ :=
  ((Finset.range t).filter (fun j => n + j * b ∈ bad)).card

theorem total_bound (starts bad : Finset ℕ) (t b : ℕ) :
    ∑ n ∈ starts, badBlocks bad t b n ≤ t * bad.card := by
  have col (j : ℕ) : (starts.filter (fun n => n + j * b ∈ bad)).card ≤ bad.card := by
    apply Finset.card_le_card_of_injOn (fun n => n + j*b)
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
    · intro x hx y hy he
      exact Nat.add_right_cancel he
  calc
    _ = ∑ j ∈ Finset.range t, (starts.filter (fun n => n + j*b ∈ bad)).card := by
      simp only [badBlocks, Finset.card_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ _j ∈ Finset.range t, bad.card := Finset.sum_le_sum (fun j _ => col j)
    _ = _ := by simp

theorem exceptional_bound (starts bad : Finset ℕ) (t b : ℕ) (ht : 0 < t) :
    (starts.filter (fun n => t ≤ 2 * badBlocks bad t b n)).card ≤ 2 * bad.card := by
  let many := starts.filter (fun n => t ≤ 2 * badBlocks bad t b n)
  change many.card ≤ _
  apply Nat.le_of_mul_le_mul_left _ ht
  calc
    t * many.card = ∑ _n ∈ many, t := by simp [Nat.mul_comm]
    _ ≤ ∑ n ∈ many, 2 * badBlocks bad t b n :=
      Finset.sum_le_sum (fun n hn => (Finset.mem_filter.mp hn).2)
    _ = 2 * ∑ n ∈ many, badBlocks bad t b n := (Finset.mul_sum ..).symm
    _ ≤ 2 * (t * bad.card) := Nat.mul_le_mul_left _ (total_bound many bad t b)
    _ = t * (2 * bad.card) := by rw [Nat.mul_left_comm]

end DensityBlocks

#print axioms DensityBlocks.exceptional_bound
```
