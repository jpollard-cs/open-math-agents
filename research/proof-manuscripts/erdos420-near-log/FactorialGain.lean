import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Tactic

/-! The change in the logarithm of the divisor count on multiplying by b. -/

namespace FactorialGain

open Finset Real
open scoped BigOperators

private theorem log_count (n : ℕ) (hn : n ≠ 0) (S : Finset ℕ) (hs : n.primeFactors ⊆ S) :
    log (n.divisors.card : ℝ) = ∑ p ∈ S, log ((n.factorization p : ℝ) + 1) := by
  rw [Nat.card_divisors hn, Nat.cast_prod]
  simp only [Nat.cast_add, Nat.cast_one]
  rw [Real.log_prod (by intros; positivity)]
  apply Finset.sum_subset hs
  intro p _ hp
  have hz : n.factorization p = 0 := Finsupp.notMem_support_iff.mp (by simpa using hp)
  simp [hz]

theorem log_count_mul (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    log ((a*b).divisors.card : ℝ) - log (a.divisors.card : ℝ) =
    ∑ p ∈ b.primeFactors, log (1 + (b.factorization p : ℝ) / ((a.factorization p : ℝ)+1)) := by
  classical
  let S := a.primeFactors ∪ b.primeFactors
  have hab : (a*b).primeFactors ⊆ S := by simp [S, Nat.primeFactors_mul ha hb]
  rw [log_count _ (Nat.mul_ne_zero ha hb) S hab, log_count _ ha S Finset.subset_union_left, ← Finset.sum_sub_distrib]
  calc
    _ = ∑ p ∈ S, log (1 + (b.factorization p : ℝ) / ((a.factorization p : ℝ)+1)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Nat.factorization_mul ha hb, Finsupp.add_apply, Nat.cast_add, ← Real.log_div (by positivity) (by positivity)]
      congr 1
      field_simp
      ring
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.subset_union_right (s₁ := a.primeFactors))
      intro p _ hp
      have hz : b.factorization p = 0 := Finsupp.notMem_support_iff.mp (by simpa using hp)
      simp [hz]

theorem factorial_step_le (n : ℕ) :
    log ((n+1).factorial.divisors.card : ℝ) - log (n.factorial.divisors.card : ℝ) ≤
    ∑ p ∈ (n+1).primeFactors, ((n+1).factorization p : ℝ) / ((n.factorial.factorization p : ℝ)+1) := by
  rw [Nat.factorial_succ, Nat.mul_comm (n+1), log_count_mul _ _ (Nat.factorial_ne_zero _) (by omega)]
  apply Finset.sum_le_sum
  intro p _
  have h := Real.log_le_sub_one_of_pos (show 0 < 1 + ((n+1).factorization p : ℝ) /
    ((n.factorial.factorization p : ℝ)+1) by positivity)
  linarith

/-- The first term in Legendre's sum suffices to bound the step. -/
theorem factorial_step_prime_mass (n : ℕ) :
    log ((n+1).factorial.divisors.card : ℝ) - log (n.factorial.divisors.card : ℝ) ≤
    ∑ p ∈ (n+1).primeFactors, (p:ℝ) * ((n+1).factorization p : ℝ) / (n+1 : ℝ) := by
  apply (factorial_step_le n).trans (Finset.sum_le_sum ?_)
  intro p hp
  have hpr := Nat.prime_of_mem_primeFactors hp
  have hleg : n / p ≤ n.factorial.factorization p := by
    rw [Nat.factorization_factorial hpr (show Nat.log p n < Nat.log p n + 2 by omega)]
    have ht : 1 ∈ Finset.Ico 1 (Nat.log p n + 2) := by simp
    simpa using (Finset.single_le_sum (f := fun i : ℕ => n / p^i) (fun _ _ => Nat.zero_le _) ht)
  have hn : n+1 ≤ p*(n.factorial.factorization p+1) := Nat.le_trans (Nat.lt_mul_div_succ n hpr.pos)
    (Nat.mul_le_mul_left p (Nat.succ_le_succ hleg))
  have hreal : (n:ℝ)+1 ≤ (p:ℝ)*((n.factorial.factorization p : ℝ)+1) := by exact_mod_cast hn
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hreal (show (0:ℝ) ≤ ((n+1).factorization p : ℝ) by positivity)]

/-- The sum of prime factors with multiplicity. -/
def primeMass (m : ℕ) : ℕ := m.factorization.sum (fun p e => e*p)

theorem primeMass_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    primeMass (a*b) = primeMass a + primeMass b := by
  rw [primeMass, Nat.factorization_mul ha hb]
  exact Finsupp.sum_add_index' (fun _ => Nat.zero_mul _) (fun _ _ _ => Nat.add_mul _ _ _)

theorem primeMass_le (m : ℕ) : primeMass m ≤ m := by
  induction m using Nat.recOnMul with
  | zero => simp [primeMass]
  | one => simp [primeMass]
  | prime p hp => simp [primeMass, hp.factorization]
  | mul a b ia ib =>
    by_cases ha : a ≤ 1
    · interval_cases a <;> simp_all [primeMass]
    by_cases hb : b ≤ 1
    · interval_cases b <;> simp_all [primeMass]
    rw [primeMass_mul (by omega) (by omega)]
    have hprod : a+b ≤ a*b := by
      by_cases hab : a ≤ b
      · have := Nat.mul_le_mul_right b (show 2 ≤ a by omega)
        omega
      · have := Nat.mul_le_mul_left a (show 2 ≤ b by omega)
        omega
    omega

/-- For any factorization into two positive factors, the mass divided by
the product is bounded by the sum of the reciprocal factors. -/
theorem primeMass_div_le_reciprocals {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (primeMass (a*b) : ℝ) / ((a:ℝ)*b) ≤ 1/(a:ℝ) + 1/(b:ℝ) := by
  rw [primeMass_mul (by omega) (by omega), Nat.cast_add]
  have h : (primeMass a : ℝ) + primeMass b ≤ (a:ℝ)+b := by exact_mod_cast Nat.add_le_add (primeMass_le a) (primeMass_le b)
  have h1 : (0:ℝ) < a := by exact_mod_cast ha
  have h2 : (0:ℝ) < b := by exact_mod_cast hb
  calc
    _ ≤ ((a:ℝ)+b)/(a*b) := div_le_div_of_nonneg_right h (by positivity)
    _ = _ := by field_simp; ring

theorem factorial_step_from_factors {n a b : ℕ} (ha : 0 < a) (hb : 0 < b) (he : n+1 = a*b) :
    log ((n+1).factorial.divisors.card : ℝ) - log (n.factorial.divisors.card : ℝ) ≤
      1/(a:ℝ) + 1/(b:ℝ) := by
  apply (factorial_step_prime_mass n).trans
  have hn : (n:ℝ)+1 = (a:ℝ)*b := by exact_mod_cast he
  rw [← Finset.sum_div]
  have hm : (∑ p ∈ (n+1).primeFactors, (p:ℝ) * ((n+1).factorization p : ℝ)) =
      (primeMass (n+1) : ℝ) := by
    simp [primeMass, Finsupp.sum, Nat.support_factorization, mul_comm]
  rw [hm, he, hn]
  exact primeMass_div_le_reciprocals ha hb

/-- If each step has a divisor between W and its square root, the gain
over the whole factorial window is at most 2h/W. -/
theorem window_log_gain_le (n h W : ℕ) (hW : 0 < W)
    (hcert : ∀ i, 1 ≤ i → i ≤ h → ∃ d, W < d ∧ d*d < n+i ∧ d ∣ n+i) :
    log ((n+h).factorial.divisors.card : ℝ) - log (n.factorial.divisors.card : ℝ) ≤
      2*(h:ℝ)/W := by
  induction h with
  | zero => simp
  | succ h ih =>
    have prev := ih (fun i hi hh => hcert i hi (by omega))
    obtain ⟨d, hWd, hds, e, he⟩ := hcert (h+1) (by omega) (by omega)
    have hde : d < e := by
      rw [he] at hds
      exact Nat.lt_of_mul_lt_mul_left hds
    have hd : 0 < d := Nat.lt_trans hW hWd
    have hepos : 0 < e := Nat.lt_trans hd hde
    have step := factorial_step_from_factors hd hepos (n := n+h) (by omega)
    have hW' : (0:ℝ) < W := by exact_mod_cast hW
    have h1 : 1/(d:ℝ) ≤ 1/(W:ℝ) := one_div_le_one_div_of_le hW' (by exact_mod_cast hWd.le)
    have h2 : 1/(e:ℝ) ≤ 1/(W:ℝ) := one_div_le_one_div_of_le hW' (by exact_mod_cast (hWd.trans hde).le)
    push_cast
    rw [show (n+(h+1)) = (n+h)+1 by omega]
    rw [mul_add, add_div, show (2:ℝ)*1/W = 1/W + 1/W by ring]
    linarith only [prev, step.trans (add_le_add h1 h2)]

end FactorialGain
