import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Optimization of the finite Fourier cutoff at exponent one half. -/

noncomputable section
namespace FactorialFourier

/-- Balancing the unsmoothed error against square-root growth in the
frequency gives the cube-root sawtooth estimate. Both degenerate cases
are included. The positive integer cutoff is available at every scale. -/
theorem optimize_half_power {R N E F : ℝ} (hN : 0 ≤ N) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (trivial : R ≤ N/2)
    (budget : ∀ H : ℕ, 1 ≤ H → R ≤ N/(2*(H:ℝ)) + 2*E*Real.sqrt H + F) :
    R ≤ 4*N^(1/3:ℝ)*E^(2/3:ℝ)+F := by
  rcases hE.eq_or_lt with he|ep
  · subst E
    rw [Real.zero_rpow (by norm_num : (2/3:ℝ) ≠ 0),mul_zero,zero_add]
    by_contra! bad
    have dp : 0 < R-F := by linarith
    obtain ⟨H,hH⟩ := exists_nat_gt (max 1 (N/(R-F)))
    have hp : 1 ≤ H := by
      have hh := (le_max_left (1:ℝ) (N/(R-F))).trans_lt hH
      exact_mod_cast hh.le
    have hc := (div_lt_iff₀ dp).mp ((le_max_right (1:ℝ) (N/(R-F))).trans_lt hH)
    have lo := budget H hp
    simp only [mul_zero,zero_mul,add_zero] at lo
    have hp' : (0:ℝ)<H := by exact_mod_cast hp
    have hi : N/(2*(H:ℝ)) < R-F := by
      apply (div_lt_iff₀ (by positivity)).mpr
      nlinarith [mul_pos hp' dp]
    linarith
  by_cases hsmall : N≤E
  · have cmp := Real.rpow_le_rpow hN hsmall (by norm_num : 0 ≤ (2/3:ℝ))
    have sep : N=N^(1/3:ℝ)*N^(2/3:ℝ) := by
      rw [← Real.rpow_add_of_nonneg hN (by norm_num) (by norm_num)]
      norm_num
    have nbound : N ≤ N^(1/3:ℝ)*E^(2/3:ℝ) := by
      calc N = _ := sep
           _ ≤ _ := mul_le_mul_of_nonneg_left cmp (by positivity)
    linarith [show 0 ≤ N^(1/3:ℝ)*E^(2/3:ℝ) by positivity]
  have np : 0<N := ep.trans_le (le_of_not_ge hsmall)
  let a : ℝ := (N/E)^(1/3:ℝ)
  have a1 : 1 ≤ a := Real.one_le_rpow ((one_le_div ep).mpr (le_of_not_ge hsmall)) (by norm_num)
  have ap : 0<a := zero_lt_one.trans_le a1
  have cube : a^3=N/E := by
    dsimp [a]
    rw [← Real.rpow_mul_natCast (div_nonneg hN hE)]
    norm_num
  have ncube := (eq_div_iff ep.ne').mp cube
  have ea : E*a = N^(1/3:ℝ)*E^(2/3:ℝ) := by
    dsimp [a]
    rw [Real.div_rpow hN hE]
    have fac : E^(1/3:ℝ)*E^(2/3:ℝ)=E := by
      rw [← Real.rpow_add ep]
      norm_num
    have en := (Real.rpow_pos_of_pos ep (1/3:ℝ)).ne'
    field_simp
    linear_combination -fac
  let H : ℕ := ⌈a^2⌉₊
  have hlo : a^2 ≤ (H:ℝ) := Nat.le_ceil _
  have hhi : (H:ℝ) < a^2+1 := Nat.ceil_lt_add_one (sq_nonneg a)
  have hHr : (1:ℝ) ≤ H := (by nlinarith [sq_nonneg (a-1)] : (1:ℝ) ≤ a^2).trans hlo
  have hH : 1 ≤ H := by exact_mod_cast hHr
  have hcut : N/(2*(H:ℝ)) ≤ E*a/2 := by
    apply (div_le_iff₀ (by linarith)).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlo (mul_nonneg hE ap.le)]
  have hs : Real.sqrt H ≤ 3*a/2 := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, by nlinarith [sq_nonneg (a-1)]⟩
  have hb := budget H hH
  calc R ≤ 4*(E*a)+F := by nlinarith [mul_le_mul_of_nonneg_left hs hE]
       _ = _ := by rw [ea]; ring

#print axioms optimize_half_power
end FactorialFourier
