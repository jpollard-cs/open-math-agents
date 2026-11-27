import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Scaling the square-root exponential-sum test after Fourier smoothing. -/
noncomputable section
namespace FactorialFourier

private lemma cube_one_third {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (1/3:ℝ))^3 = x := by
  rw [← Real.rpow_mul_natCast hx]; norm_num

private lemma cube_two_thirds {x : ℝ} (hx : 0 ≤ x) :
    (x ^ (2/3:ℝ))^3 = x^2 := by
  rw [← Real.rpow_mul_natCast hx]; norm_num

/-- The interval length and the square-root coefficient cancel all powers
of u in the fractional-power part of the sawtooth estimate. -/
theorem scale_one_third {N x t u : ℝ} (hN : 0 ≤ N) (hx : 0 ≤ x) (ht : 0 < t)
    (hu : 0 < u) (len : N ≤ 3*u/t) :
    4*N^(1/3:ℝ)*(335*Real.sqrt (x/u))^(2/3:ℝ) ≤ 280*(x/t)^(1/3:ℝ) := by
  have X : 0 ≤ x/u := div_nonneg hx hu.le
  have coeff : 0 ≤ 335*Real.sqrt (x/u) := by positivity
  have main : N*(x/u) ≤ 3*x/t := by
    apply (mul_le_mul_of_nonneg_right len X).trans
    apply le_of_eq; field_simp
  have l : (4*N^(1/3:ℝ)*(335*Real.sqrt (x/u))^(2/3:ℝ))^3 =
      (4:ℝ)^3*335^2*(N*(x/u)) := by
    rw [mul_pow,mul_pow,cube_one_third hN,cube_two_thirds coeff,mul_pow, Real.sq_sqrt X]
    ring
  have r : (280*(x/t)^(1/3:ℝ))^3 = 280^3*(x/t) := by
    rw [mul_pow,cube_one_third (div_nonneg hx ht.le)]
  have non : 0≤x/t := div_nonneg hx ht.le
  by_contra! contra
  have pow := pow_lt_pow_left₀ contra (show 0 ≤ 280*(x/t)^(1/3:ℝ) by positivity) (by decide : 3≠0)
  rw [l,r] at pow
  rw [mul_div_assoc] at main
  linarith

end FactorialFourier
#print axioms FactorialFourier.scale_one_third
