import Mathlib

/-! Exact finite averaging in the cofactor estimate of the density manuscript.
Codex (AI) at the request of Jordan Pollard. -/
namespace FactorialDensity
open Finset

/-- A bound for one ordinary offset. S is the set of successful starts,
q its assigned guard prime (only positivity and divisibility are needed).
M bounds the number of successful starts with any individual small cofactor. -/
theorem guarded_column (S : Finset ℕ) (R : ℕ → ℕ) (q L : ℕ) (M : ℝ)
    (hq : 0 < q) (pos : ∀ t ∈ S, 0 < R t)
    (guard : ∀ t ∈ S, R t ≤ L → q ∣ R t)
    (cap : ∀ a ∈ Icc 1 L, ((S.filter (fun t => R t=q*a)).card:ℝ) ≤ M) :
    (∑ t ∈ S,(1:ℝ)/R t) ≤
      (S.card:ℝ)/(L+1) + (M/q)*∑ a ∈ Icc 1 L,(1:ℝ)/a := by
  let hit (t a : ℕ) : ℝ := if R t=q*a then 1/((q:ℝ)*a) else 0
  have nonneg (t a : ℕ) : 0 ≤ hit t a := by unfold hit; split <;> positivity
  have row (t : ℕ) (ht : t ∈ S) :
      (1:ℝ)/R t ≤ 1/(L+1) + ∑ a ∈ Icc 1 L,hit t a := by
    by_cases big : L < R t
    · have lower : (L:ℝ)+1 ≤ R t := by exact_mod_cast big
      have le := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1) (by positivity) lower
      exact le.trans (le_add_of_nonneg_right (sum_nonneg fun a _ => nonneg t a))
    · have small := Nat.le_of_not_gt big
      obtain ⟨a,ha⟩ := guard t ht small
      have posA : 1 ≤ a := by
        by_contra! hn
        have az : a=0 := by omega
        have := pos t ht
        simp [az] at ha
        omega
      have leR : a ≤ R t := by
        rw [ha]
        simpa using Nat.mul_le_mul_right a hq
      have mem := mem_Icc.mpr ⟨posA,leR.trans small⟩
      have one := single_le_sum (f:=hit t) (fun b _ => nonneg t b) mem
      have eq : hit t a = (1:ℝ)/R t := by simp [hit,ha,Nat.cast_mul]
      rw [eq] at one
      exact one.trans (le_add_of_nonneg_left (by positivity))
  have subtotal := sum_le_sum row
  rw [sum_add_distrib,sum_const,nsmul_eq_mul,sum_comm] at subtotal
  have column (a : ℕ) (ha : a ∈ Icc 1 L) :
      (∑ t ∈ S,hit t a) ≤ (M/q)*(1/(a:ℝ)) := by
    change (∑ t ∈ S,if R t=q*a then 1/((q:ℝ)*a) else 0) ≤ _
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    calc
      _ ≤ M*(1/((q:ℝ)*a)) := mul_le_mul_of_nonneg_right (cap a ha) (by positivity)
      _ = _ := by ring
  have total := subtotal.trans (add_le_add le_rfl (sum_le_sum column))
  rw [← mul_sum] at total
  simpa only [mul_one_div] using total

/-- The same successful start is used at every offset; the cap H is a
bound on the total mass divided by the number of successful starts. -/
theorem simultaneous (S J : Finset ℕ) (R : ℕ → ℕ → ℕ) (H : ℝ) (hs : S.Nonempty)
    (bound : (∑ j ∈ J,∑ t ∈ S,(1:ℝ)/R t j) ≤ (S.card:ℝ)*H) :
    ∃ t ∈ S, (∑ j ∈ J,(1:ℝ)/R t j) ≤ H := by
  apply Finset.exists_le_of_sum_le hs
  rw [sum_comm,sum_const,nsmul_eq_mul]
  exact bound

end FactorialDensity
#print axioms FactorialDensity.guarded_column
#print axioms FactorialDensity.simultaneous
