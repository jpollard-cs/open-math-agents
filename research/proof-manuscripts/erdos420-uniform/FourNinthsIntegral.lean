import Mathlib

/-! A rational certificate for the last integral in the proof of Lemma 3 of
Erdős, Graham, Ivić and Pomerance, *On the number of divisors of n!* (1996).
The three intervals and exponent pairs below are those of their equation (19).
The estimate here concerns the integral itself, without any sieve hypotheses. -/

noncomputable section
open MeasureTheory Set Real
open scoped Interval

namespace FourNinthsIntegral

/-- The integrand u θ(u,k,l) for c = 4/9. -/
def integrand (k l u : ℝ) : ℝ :=
  2 * (1 + k - l) * u / (4/9 + (4/9)*k - k + (k-l)*u)

/-- The three consecutive exponent-pair ranges in the paper. -/
def sieveIntegral : ℝ :=
  (∫ u in (4/9 : ℝ)..77/162, integrand (1/14) (11/14) u) +
  (∫ u in (77/162 : ℝ)..29/54, integrand (1/6) (2/3) u) +
  (∫ u in (29/54 : ℝ)..50009/90000, integrand (1/2) (1/2) u)

private lemma band (K A B a b : ℝ) (hab : a ≤ b) (hB : 0 < B) (hb : 0 < A-B*b) :
    (∫ x in a..b, K*x/(A-B*x)) =
      K*A/B^2 * log ((A-B*a)/(A-B*b)) - K/B*(b-a) := by
  have den (x : ℝ) (hx : x ∈ [[a,b]]) : 0 < A-B*x := by
    rw [uIcc_of_le hab] at hx
    nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hx.2)]
  let F := fun x : ℝ => -(K*A/B^2) * log (A-B*x) - K/B*x
  have hd (x : ℝ) (hx : x ∈ [[a,b]]) : HasDerivAt F (K*x/(A-B*x)) x := by
    have h := ((hasDerivAt_const x A).sub ((hasDerivAt_id x).const_mul B)).log (den x hx).ne'
    have hh := (h.const_mul (-(K*A/B^2))).sub ((hasDerivAt_id x).const_mul (K/B))
    apply hh.congr_deriv
    change -(K*A/B^2)*((0-B*1)/(A-B*x)) - K/B*1 = K*x/(A-B*x)
    field_simp [hB.ne', (den x hx).ne']
    ring
  have hc : ContinuousOn (fun x : ℝ => K*x/(A-B*x)) [[a,b]] :=
    (continuous_const.mul continuous_id).continuousOn.div
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousOn
      (fun x hx => (den x hx).ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable, Real.log_div
    (den a (left_mem_uIcc)).ne' hb.ne']
  dsimp [F]
  ring

theorem evaluated :
    4/9 + sieveIntegral =
      4/9 + ((4/7)*(17/42)/(5/7)^2 * log (99/74) - (4/7)/(5/7)*(77/162-4/9)) +
      ((19/54)/(1/2)^2 * log (37/27) - 1/(1/2)*(29/54-77/162)) +
      6*((50009/90000)^2-(29/54)^2) := by
  have first (u : ℝ) : integrand (1/14) (11/14) u = (4/7)*u/(17/42-(5/7)*u) := by
    unfold integrand
    congr 1 <;> ring
  have second (u : ℝ) : integrand (1/6) (2/3) u = 1*u/(19/54-(1/2)*u) := by
    unfold integrand
    congr 1 <;> ring
  have third (u : ℝ) : integrand (1/2) (1/2) u = 12*u := by
    unfold integrand
    ring
  unfold sieveIntegral
  simp_rw [first, second, third]
  rw [band _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num),
      band _ _ _ _ _ (by norm_num) (by norm_num) (by norm_num),
      intervalIntegral.integral_const_mul, integral_id]
  norm_num
  ring

/-- In particular the coefficient still available for large primes exceeds 0.00624. -/
theorem certified : 4/9 + sieveIntegral < 993755/1000000 := by
  have h₁ := Real.log_div_le_sum_range_add (x := 25/173) (by norm_num) (by norm_num) 4
  have h₂ := Real.log_div_le_sum_range_add (x := 5/32) (by norm_num) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h₁ h₂
  rw [evaluated]
  norm_num
  linarith only [h₁, h₂]

end FourNinthsIntegral
#print axioms FourNinthsIntegral.certified
