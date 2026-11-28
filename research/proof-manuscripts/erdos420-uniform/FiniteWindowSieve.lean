import Mathlib

/-! The finite Λ² majorant used in equations (14)–(15) of the factorial
divisor paper, with integer endpoints and arbitrary real signed weights. -/
noncomputable section
open Finset

namespace FiniteWindowSieve

/-- An exact finite upper sieve. Here N(m) is any nonnegative multiplicity
(e.g. the number of multiples of m in the short interval), S is the block
of moduli, and D is the support of the level weights, containing 1. -/
theorem lcm_majorant (S D : Finset ℕ) (N w : ℕ → ℝ)
    (hN : ∀ m ∈ S, 0 ≤ N m) (h1 : 1 ∈ D) (hw : w 1 = 1)
    (sifted : Finset ℕ) (hsub : sifted ⊆ S)
    (hrough : ∀ m ∈ sifted, ∀ d ∈ D, d ∣ m → d = 1) :
    (∑ m ∈ sifted, N m) ≤
      ∑ d ∈ D, ∑ e ∈ D, w d * w e *
        (∑ m ∈ S, if Nat.lcm d e ∣ m then N m else 0) := by
  let W (d m : ℕ) := if d ∣ m then w d else 0
  have exact_one (m : ℕ) (hm : m ∈ sifted) : (∑ d ∈ D, W d m) = 1 := by
    rw [sum_eq_single_of_mem 1 h1]
    · simp [W, hw]
    · intro d hd hne
      exact if_neg (fun h => hne (hrough m hm d hd h))
  calc
    (∑ m ∈ sifted, N m) = ∑ m ∈ sifted, N m * (∑ d ∈ D, W d m)^2 := by
      apply sum_congr rfl
      intro m hm
      simp [exact_one m hm]
    _ ≤ ∑ m ∈ S, N m * (∑ d ∈ D, W d m)^2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => mul_nonneg (hN m hm) (sq_nonneg _))
    _ = ∑ d ∈ D, ∑ e ∈ D, w d * w e *
        (∑ m ∈ S, if Nat.lcm d e ∣ m then N m else 0) := by
      simp_rw [sq, sum_mul, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro d hd
      rw [sum_comm]
      apply sum_congr rfl
      intro e he
      apply sum_congr rfl
      intro m hm
      by_cases hdm : d ∣ m <;> by_cases hem : e ∣ m <;>
        simp [W, Nat.lcm_dvd_iff, hdm, hem]
      ring

/-- In a block entirely above the level, every prime passes the upper sieve. -/
theorem prime_block (S D : Finset ℕ) (N w : ℕ → ℝ) (z : ℕ)
    (hN : ∀ m ∈ S, 0 ≤ N m) (h1 : 1 ∈ D) (hw : w 1 = 1)
    (hD : ∀ d ∈ D, d ≤ z) (hS : ∀ m ∈ S, z < m) :
    (∑ p ∈ S.filter Nat.Prime, N p) ≤
      ∑ d ∈ D, ∑ e ∈ D, w d * w e *
        (∑ m ∈ S, if Nat.lcm d e ∣ m then N m else 0) := by
  apply lcm_majorant S D N w hN h1 hw _ (filter_subset _ _)
  intro m hm d hd hdm
  obtain ⟨hs, hp⟩ := mem_filter.mp hm
  rcases (Nat.dvd_prime hp).mp hdm with hone | heq
  · exact hone
  · have := hD d hd
    have := hS m hs
    omega

end FiniteWindowSieve
#print axioms FiniteWindowSieve.prime_block
