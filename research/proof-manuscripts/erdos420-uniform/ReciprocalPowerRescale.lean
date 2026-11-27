import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Rescale a cutoff-optimized exponential-sum estimate on reciprocal multiples. -/
noncomputable section
open Real
namespace FactorialFourier

/-- The length of the grid and the size of the exponential coefficient
combine to give the modulus exponent −l/(1+k). -/
theorem rescale_local_power {N E K x u t k l : ℝ} (hN : 0≤N) (hE : 0≤E)
    (hK : 1≤K) (hx : 0<x) (hu : 0<u) (ht : 0<t) (hk : 0≤k)
    (count : N ≤ 3*u/t) (amplitude : E ≤ K*x^k*u^(l-2*k)*t^(k-l)) :
    N^(k/(1+k))*E^(1/(1+k)) ≤
      (3*K)*x^(k/(1+k))*u^((l-k)/(1+k))*t^(-l/(1+k)) := by
  let a := k/(1+k)
  let b := 1/(1+k)
  have den : 0<1+k := by linarith
  have a0 : 0≤a := div_nonneg hk den.le
  have b0 : 0≤b := div_nonneg zero_le_one den.le
  have a1 : a≤1 := (div_le_one den).mpr (by linarith)
  have b1 : b≤1 := (div_le_one den).mpr (by linarith)
  have K0 : 0≤K := zero_le_one.trans hK
  have a3 : (3:ℝ)^a ≤ 3 := by simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3) a1
  have bK : K^b ≤ K := by simpa using Real.rpow_le_rpow_of_exponent_le hK b1
  have r1 : k*b=a := by dsimp [a,b]; ring
  have r2 : a+(l-2*k)*b=(l-k)/(1+k) := by dsimp [a,b]; ring
  have r3 : -a+(k-l)*b = -l/(1+k) := by dsimp [a,b]; ring
  have tt : (t^a)⁻¹ = t^(-a) := (Real.rpow_neg ht.le a).symm
  calc
    N^a*E^b ≤ (3*u/t)^a*(K*x^k*u^(l-2*k)*t^(k-l))^b := by gcongr
    _ = (3^a*K^b)*x^a*u^((l-k)/(1+k))*t^(-l/(1+k)) := by
      rw [Real.div_rpow (by positivity) ht.le,Real.mul_rpow (by norm_num) hu.le,
        Real.mul_rpow (by positivity) (Real.rpow_nonneg ht.le _),
        Real.mul_rpow (by positivity) (Real.rpow_nonneg hu.le _),Real.mul_rpow K0 (Real.rpow_nonneg hx.le _),
        ← Real.rpow_mul hx.le,← Real.rpow_mul hu.le,← Real.rpow_mul ht.le,
        r1,← r2,← r3,Real.rpow_add hu,Real.rpow_add ht,div_eq_mul_inv,tt]
      ring
    _ ≤ _ := by gcongr

#print axioms rescale_local_power
end FactorialFourier
