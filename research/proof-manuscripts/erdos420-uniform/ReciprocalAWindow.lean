import ReciprocalWindowExponential

/-! Passage from an exponent pair for a real-base reciprocal phase to
the positive-frequency bound on a sieve interval. -/
noncomputable section
open Finset Real
namespace FactorialFourier

private theorem complex_multiples (u v : ℝ) (t : ℕ) (ht : 0 < t) (f : ℕ → ℂ) :
    (∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·), f m) =
      ∑ q ∈ Ioc ⌊u/(t:ℝ)⌋₊ ⌊v/(t:ℝ)⌋₊, f (q*t) := by
  rw [sum_filter]
  apply Complex.ext
  · simp only [Complex.re_sum,apply_ite Complex.re, Complex.zero_re]
    exact FactorialRounding.sum_multiples u v t ht (fun j => (f j).re)
  · simp only [Complex.im_sum,apply_ite Complex.im, Complex.zero_im]
    exact FactorialRounding.sum_multiples u v t ht (fun j => (f j).im)

/-- An exponential-sum bound for positive frequencies on the exact set
of multiples. The power exponents satisfy 0 ≤ l−2k ≤ 1 for both A-pairs. -/
theorem window_exponential_of_pair {k l C u v : ℝ} {x t j : ℕ}
    (block : ∀ {B Y : ℝ} (N : ℕ), 1 ≤ B → 0 < Y → (N:ℝ) ≤ 2*B+1 →
      ‖∑ i ∈ range N, ReciprocalFirstDerivative.wave (Y/(B+i))‖ ≤
        C*(B^l*(Y/B^2)^k+B^2/Y))
    (hC : 0 ≤ C) (hlo : 0 ≤ l-2*k) (hhi : l-2*k ≤ 1)
    (hx : 0 < x) (ht : 0 < t) (hj : 0 < j) (htu : (t:ℝ) ≤ u) (huv : u ≤ v)
    (hv : v ≤ 3*u) :
    ‖∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·), Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/m)‖ ≤
      ((2*C)*(x:ℝ)^k*u^(l-2*k)*(t:ℝ)^(k-l))*(j:ℝ)^k + ((4*C)*u^2/((x:ℝ)*t))/j := by
  let M := ⌊u/(t:ℝ)⌋₊+1
  let b := ⌊v/(t:ℝ)⌋₊
  let N := b+1-M
  let Y := (j:ℝ)*x/t
  have tp : (0:ℝ) < t := by exact_mod_cast ht
  have xp : (0:ℝ) < x := by exact_mod_cast hx
  have jp : (0:ℝ) < j := by exact_mod_cast hj
  have up := tp.trans_le htu
  have yp : 0 < Y := by dsimp [Y]; positivity
  have mn : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le _)
  have mp : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have ml : u/t ≤ (M:ℝ) := by simpa only [M,Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (u/(t:ℝ))).le
  have mu : (M:ℝ) ≤ 2*(u/t) := by
    simp only [M,Nat.cast_add,Nat.cast_one]
    linarith [Nat.floor_le (div_nonneg up.le tp.le), (one_le_div tp).mpr htu]
  have b3 : b ≤ 3*M := by
    have h₁ : (b:ℝ) ≤ v/t := Nat.floor_le (div_nonneg (up.le.trans huv) tp.le)
    have h₂ : v/t ≤ 3*(u/t) := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hv tp.le
    exact_mod_cast (show (b:ℝ) ≤ 3*(M:ℝ) by linarith)
  have len : (N:ℝ) ≤ 2*(M:ℝ)+1 := by
    exact_mod_cast (show N ≤ 2*M+1 by dsimp [N]; omega)
  have eq (a : ℕ) :
      Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/(((M+a)*t:ℕ):ℂ)) =
        ReciprocalFirstDerivative.wave (Y/((M:ℝ)+a)) := by
    unfold ReciprocalFirstDerivative.wave
    congr 1
    dsimp [Y]; push_cast; simp only [div_eq_mul_inv,mul_inv_rev]; ring
  rw [complex_multiples u v t ht,← Icc_succ_left_eq_Ioc,← Ico_add_one_right_eq_Icc,
    Finset.sum_Ico_eq_sum_range]
  change ‖∑ a ∈ range N, Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/(((M+a)*t:ℕ):ℂ))‖ ≤ _
  simp only [eq]
  apply (block N (by exact_mod_cast mn : (1:ℝ) ≤ M) yp len).trans
  have hir : (M:ℝ)^2/Y ≤ (4*u^2/((x:ℝ)*t))/j := by
    apply (div_le_div_of_nonneg_right (pow_le_pow_left₀ mp.le mu 2) yp.le).trans_eq
    dsimp [Y]; field_simp; ring
  have id : (M:ℝ)^l*(Y/(M:ℝ)^2)^k = Y^k*(M:ℝ)^(l-2*k) := by
    rw [Real.div_rpow yp.le (sq_nonneg _),← Real.rpow_natCast_mul mp.le 2 k,Real.rpow_sub mp]
    norm_num
    ring
  have pwr : (M:ℝ)^(l-2*k) ≤ 2*(u/t)^(l-2*k) := by
    apply (Real.rpow_le_rpow mp.le mu hlo).trans
    rw [Real.mul_rpow zero_le_two (by positivity : 0 ≤ u/(t:ℝ))]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    simpa using (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hhi)
  have powers : Y^k * (2*(u/t)^(l-2*k)) =
      2*(x:ℝ)^k*u^(l-2*k)*(t:ℝ)^(k-l)*(j:ℝ)^k := by
    dsimp only [Y]
    rw [Real.div_rpow (mul_pos jp xp).le tp.le,Real.mul_rpow jp.le xp.le,
        Real.div_rpow up.le tp.le]
    have den : (t:ℝ)^k*(t:ℝ)^(l-2*k) = (t:ℝ)^(l-k) := by
      rw [← Real.rpow_add tp]
      congr 1
      ring
    rw [show k-l = -(l-k) by ring,Real.rpow_neg tp.le,← den]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have main : (M:ℝ)^l*(Y/(M:ℝ)^2)^k ≤
      2*(x:ℝ)^k*u^(l-2*k)*(t:ℝ)^(k-l)*(j:ℝ)^k := by
    rw [id,← powers]
    exact mul_le_mul_of_nonneg_left pwr (by positivity)
  apply (mul_le_mul_of_nonneg_left (add_le_add main hir) hC).trans_eq
  ring

end FactorialFourier
#print axioms FactorialFourier.window_exponential_of_pair
