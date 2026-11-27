import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! A finite van der Corput differencing inequality. Shift averaging on the zero
extension preserves the endpoints of every correlation, including empty overlaps.
The normalization is the one used for the A-process of exponent pairs.
See S. W. Graham and G. Kolesnik, *Van der Corput's Method of Exponential Sums*,
Chapter 2. -/

noncomputable section
open Finset
open scoped ComplexConjugate

namespace FactorialDifferencing

/-- The correlation at lag d in a sequence of length N. -/
def corr (f : ℕ → ℂ) (N d : ℕ) : ℂ :=
  ∑ j ∈ range (N-d), f (j+d) * conj (f j)

private def shift (f : ℕ → ℂ) (N h x : ℕ) : ℂ :=
  if x ∈ Ico h (h+N) then f (x-h) else 0

private theorem sum_shift (f : ℕ → ℂ) (N h M : ℕ) (end_le : h+N ≤ M) :
    ∑ x ∈ range M, shift f N h x = ∑ j ∈ range N, f j := by
  have sub : Ico h (h+N) ⊆ range M := by
    intro x hx
    exact mem_range.mpr ((mem_Ico.mp hx).2.trans_le end_le)
  calc
    _ = ∑ x ∈ Ico h (h+N), shift f N h x := by
      symm
      exact sum_subset sub (by intro x _ hx; simp [shift,hx])
    _ = ∑ x ∈ Ico h (h+N), f (x-h) :=
      sum_congr rfl (by intro x hx; simp [shift,hx])
    _ = _ := by rw [sum_Ico_eq_sum_range]; simp

private theorem shift_mul (f : ℕ → ℂ) (N k h x : ℕ) (hk : k ≤ h) :
    shift f N k x * conj (shift f N h x) =
      shift (fun j => f (j+(h-k))*conj (f j)) (N-(h-k)) h x := by
  by_cases h₁ : x ∈ Ico k (k+N) <;> by_cases h₂ : x ∈ Ico h (h+N)
  · have h₃ : x ∈ Ico h (h+(N-(h-k))) := by
      simp only [mem_Ico] at *; omega
    simp only [shift, if_pos h₁, if_pos h₂, if_pos h₃]
    rw [show x-h+(h-k)=x-k by have := (mem_Ico.mp h₂).1; omega]
  · have h₃ : x ∉ Ico h (h+(N-(h-k))) := by
      simp only [mem_Ico] at *; omega
    simp [shift,h₂,h₃]
  · have h₃ : x ∉ Ico h (h+(N-(h-k))) := by
      simp only [mem_Ico] at *; omega
    simp [shift,h₁,h₃]
  · have h₃ : x ∉ Ico h (h+(N-(h-k))) := by
      simp only [mem_Ico] at *; omega
    simp [shift,h₂,h₃]

private theorem shift_overlap (f : ℕ → ℂ) (N k h M : ℕ)
    (hk : k ≤ h) (hM : h+N ≤ M) :
    ∑ x ∈ range M, shift f N k x * conj (shift f N h x) = corr f N (h-k) := by
  simp_rw [shift_mul f N k h _ hk]
  exact sum_shift _ _ _ _ (by omega)

private theorem norm_square_expand (g : ℕ → ℂ) (H : ℕ) :
    ‖∑ h ∈ range H, g h‖^2 =
      (∑ h ∈ range H, ‖g h‖^2) +
        2*∑ h ∈ range H, ∑ k ∈ range h, (g k * conj (g h)).re := by
  induction H with
  | zero => simp
  | succ H ih =>
    have pair (z w : ℂ) : ‖z+w‖^2 = ‖z‖^2+‖w‖^2+2*(z*conj w).re := by
      simp [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re]
      ring
    rw [sum_range_succ, pair, ih, sum_range_succ (f := fun h => ‖g h‖^2),
      sum_range_succ (f := fun h => ∑ k ∈ range h, (g k * conj (g h)).re)]
    rw [sum_mul, Complex.re_sum]
    ring

private theorem square_cs (g : ℕ → ℂ) (M : ℕ) :
    ‖∑ x ∈ range M, g x‖^2 ≤ (M:ℝ) * ∑ x ∈ range M, ‖g x‖^2 := by
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le (range M) g) 2).trans
  simpa using sq_sum_le_card_mul_sum_sq (s := range M) (f := fun x => ‖g x‖)

private theorem zero_corr (f : ℕ → ℂ) (N : ℕ) :
    (corr f N 0).re = ∑ j ∈ range N, ‖f j‖^2 := by
  simp only [corr, Nat.sub_zero, Nat.add_zero, Complex.re_sum, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- Sharp finite shift averaging, with the real part of each correlation and
the exact Cauchy--Schwarz prefactor N+H-1. No relation between H and N is needed. -/
theorem differencing_triangle (f : ℕ → ℂ) (N H : ℕ) :
    (H:ℝ)^2 * ‖∑ j ∈ range N, f j‖^2 ≤
      ((N+H-1:ℕ):ℝ)*((H:ℝ)*(∑ j ∈ range N, ‖f j‖^2) +
        2*∑ h ∈ range H, ∑ k ∈ range h, (corr f N (h-k)).re) := by
  let M := N+H-1
  let w (x : ℕ) := ∑ h ∈ range H, shift f N h x
  have avg : ∑ x ∈ range M, w x = (H:ℂ)*(∑ j ∈ range N, f j) := by
    dsimp only [w]
    rw [sum_comm]
    calc
      _ = ∑ _h ∈ range H, ∑ j ∈ range N, f j := by
        apply sum_congr rfl; intro h hh
        exact sum_shift f N h M (by dsimp [M]; have := mem_range.mp hh; omega)
      _ = _ := by simp
  have diag (h : ℕ) (hh : h ∈ range H) :
      ∑ x ∈ range M, ‖shift f N h x‖^2 = ∑ j ∈ range N, ‖f j‖^2 := by
    have eq := congrArg Complex.re (shift_overlap f N h h M le_rfl (by
      dsimp [M]; have := mem_range.mp hh; omega))
    simpa only [Complex.re_sum,Complex.mul_conj',← Complex.ofReal_pow,Complex.ofReal_re,Nat.sub_self,zero_corr] using eq
  have off (k h : ℕ) (hk : k ∈ range h) (hh : h ∈ range H) :
      ∑ x ∈ range M, (shift f N k x * conj (shift f N h x)).re = (corr f N (h-k)).re := by
    rw [← Complex.re_sum]
    exact congrArg Complex.re (shift_overlap f N k h M (mem_range.mp hk).le (by
      dsimp [M]; have := mem_range.mp hh; omega))
  have energy : ∑ x ∈ range M, ‖w x‖^2 =
      (H:ℝ)*(∑ j ∈ range N, ‖f j‖^2) +
      2*∑ h ∈ range H, ∑ k ∈ range h, (corr f N (h-k)).re := by
    dsimp only [w]
    simp_rw [norm_square_expand]
    rw [sum_add_distrib, ← mul_sum, sum_comm]
    congr 1
    · calc _ = ∑ _h ∈ range H, ∑ j ∈ range N, ‖f j‖^2 :=
                  sum_congr rfl (fun h hh => diag h hh)
           _ = _ := by simp
    · congr 1
      rw [sum_comm]
      apply sum_congr rfl; intro h hh
      rw [sum_comm]
      exact sum_congr rfl (fun k hk => off k h hk hh)
  have bound := square_cs w M
  rw [avg, norm_mul, mul_pow, energy] at bound
  simpa [M, Complex.norm_natCast] using bound


private theorem count_lags (F : ℕ → ℝ) (H : ℕ) :
    (∑ h ∈ range H, ∑ k ∈ range h, F (h-k)) =
      ∑ d ∈ range H, ((H-(d+1):ℕ):ℝ)*F (d+1) := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ, ih, sum_range_succ (f := fun d => ((H+1-(d+1):ℕ):ℝ)*F (d+1))]
    simp only [Nat.sub_self, Nat.cast_zero, zero_mul, add_zero]
    have reflected : (∑ k ∈ range H, F (H-k)) = ∑ d ∈ range H, F (d+1) := by
      rw [← sum_range_reflect (fun d => F (d+1)) H]
      apply sum_congr rfl
      intro k hk
      have := mem_range.mp hk
      congr 1
      omega
    rw [reflected, ← sum_add_distrib]
    apply sum_congr rfl
    intro d hd
    have e : H+1-(d+1) = (H-(d+1))+1 := by have := mem_range.mp hd; omega
    rw [e, Nat.cast_succ]
    ring

/-- Finite van der Corput inequality with all overlapping pairs grouped by lag.
The multiplicity of lag d is H-d. Zero-length sequences and shifts past the
end are allowed. -/
theorem differencing (f : ℕ → ℂ) (N H : ℕ) :
    (H:ℝ)^2 * ‖∑ j ∈ range N, f j‖^2 ≤
      ((N+H-1:ℕ):ℝ)*((H:ℝ)*(∑ j ∈ range N, ‖f j‖^2) +
        2*∑ d ∈ range H, ((H-(d+1):ℕ):ℝ)*‖corr f N (d+1)‖) := by
  have h := differencing_triangle f N H
  rw [count_lags (fun d => (corr f N d).re)] at h
  apply h.trans
  gcongr with d hd
  exact Complex.re_le_norm _

/-- The additive character e(x)=exp(2πix). -/
def character (x : ℝ) : ℂ := Complex.exp (((2*Real.pi*x : ℝ):ℂ)*Complex.I)

private theorem character_diff (x y : ℝ) :
    character x * conj (character y) = character (x-y) := by
  unfold character
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- One A-process step for the exponential sum of a real phase. The new
phase is the first finite difference on the exact common interval. -/
theorem exponential_differencing (p : ℕ → ℝ) (N H : ℕ) :
    (H:ℝ)^2 * ‖∑ j ∈ range N, character (p j)‖^2 ≤
      ((N+H-1:ℕ):ℝ)*((H:ℝ)*N +
        2*∑ d ∈ range H, ((H-(d+1):ℕ):ℝ)*
          ‖∑ j ∈ range (N-(d+1)), character (p (j+(d+1))-p j)‖) := by
  simpa only [corr, character_diff, show ∀ x, ‖character x‖=1 from
    fun x => Complex.norm_exp_ofReal_mul_I _, one_pow, sum_const, card_range,
    nsmul_eq_mul,mul_one] using differencing (fun j => character (p j)) N H

private theorem triangular_number (H : ℕ) :
    2*(∑ j ∈ range H, (j:ℝ)) = (H:ℝ)*((H:ℝ)-1) := by
  induction H with
  | zero => simp
  | succ n ih => rw [sum_range_succ, Nat.cast_succ]; nlinarith only [ih]

/-- Uniform differenced-sum form. Any common bound on the nonzero shifts
can be fed directly to this inequality before optimizing the integer H. -/
theorem uniform_differencing (p : ℕ → ℝ) (N H : ℕ) (hH : 1 ≤ H) (E : ℝ)
    (bound : ∀ d, 0 < d → d < H →
      ‖∑ j ∈ range (N-d), character (p (j+d) - p j)‖ ≤ E) :
    (H:ℝ)*‖∑ j ∈ range N, character (p j)‖^2 ≤
      ((N+H-1:ℕ):ℝ)*((N:ℝ) + ((H:ℝ)-1)*E) := by
  let f := fun j => character (p j)
  have b := differencing_triangle f N H
  have diag : (∑ j ∈ range N, ‖f j‖^2) = (N:ℝ) := by
    have char_unit (x : ℝ) : ‖character x‖=1 := Complex.norm_exp_ofReal_mul_I _
    simp only [f, char_unit, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [diag] at b
  have each (h : ℕ) (hh : h ∈ range H) : (∑ k ∈ range h, (corr f N (h-k)).re) ≤ (h:ℝ)*E := by
    calc _ ≤ ∑ _k ∈ range h, E := by
           apply sum_le_sum
           intro k hk
           apply (Complex.re_le_norm _).trans
           have dpos : 0 < h-k := by have := mem_range.mp hk; omega
           have dlt : h-k < H := (Nat.sub_le ..).trans_lt (mem_range.mp hh)
           simpa [corr, f, character_diff] using bound _ dpos dlt
         _ = _ := by simp
  have tri := mul_le_mul_of_nonneg_left (sum_le_sum each) (show (0:ℝ) ≤ 2 by norm_num)
  rw [← sum_mul] at tri
  have tri' : 2*(∑ h ∈ range H, ∑ k ∈ range h, (corr f N (h-k)).re)
       ≤ (H:ℝ)*((H:ℝ)-1)*E := by
    calc _ ≤ _ := tri
         _ = _ := by rw [← mul_assoc, triangular_number]
  have pos : 0 < (H:ℝ) := by exact_mod_cast (show 0 < H by omega)
  apply (mul_le_mul_iff_right₀ pos).mp
  calc
    _ = (H:ℝ)^2 * ‖∑ j ∈ range N, f j‖^2 := by dsimp [f]; ring
    _ ≤ _ := b
    _ ≤ ((N+H-1:ℕ):ℝ)*((H:ℝ)*N + ((H:ℝ)*((H:ℝ)-1)*E)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl tri') (Nat.cast_nonneg _)
    _ = _ := by ring

/-- One A-step with both a uniform oscillatory term P and the reciprocal-lag
error B/d. Summing the latter only spends a harmonic factor. -/
theorem differencing_with_inverse_lag (p : ℕ → ℝ) (N H : ℕ) (hH : 1 ≤ H)
    {P B : ℝ} (hP : 0 ≤ P) (hB : 0 ≤ B)
    (bound : ∀ d, 0 < d → d < H →
      ‖∑ j ∈ range (N-d), character (p (j+d)-p j)‖ ≤ P+B/d) :
    (H:ℝ) * ‖∑ j ∈ range N, character (p j)‖^2 ≤
      ((N+H-1:ℕ):ℝ)*((N:ℝ)+2*((H:ℝ)*P+B*(1+Real.log H))) := by
  let E (d : ℕ) := ‖∑ j ∈ range (N-d), character (p (j+d)-p j)‖
  have each_lag (d : ℕ) (hd : d ∈ range H) :
      ((H-(d+1):ℕ):ℝ)*E (d+1) ≤ (H:ℝ)*(P+B/((d+1:ℕ):ℝ)) := by
    have leH : d+1 ≤ H := mem_range.mp hd
    by_cases eqH : d+1 = H
    · rw [eqH, Nat.sub_self, Nat.cast_zero, zero_mul]
      positivity
    · have posd : 0 < d+1 := Nat.succ_pos _
      exact mul_le_mul (by exact_mod_cast Nat.sub_le H (d+1))
        (bound _ posd (lt_of_le_of_ne leH eqH)) (norm_nonneg _) (Nat.cast_nonneg _)
  have sum_inv : (∑ d ∈ range H, ((d+1:ℕ):ℝ)⁻¹) = (harmonic H:ℝ) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  have est : (∑ d ∈ range H, ((H-(d+1):ℕ):ℝ)*E (d+1)) ≤
      (H:ℝ)*((H:ℝ)*P+B*(1+Real.log H)) := by
    apply (sum_le_sum each_lag).trans
    rw [← mul_sum]
    simp only [div_eq_mul_inv,sum_add_distrib,← mul_sum,sum_inv,sum_const,card_range,
      nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log H) hB)) (Nat.cast_nonneg _)
  have base := exponential_differencing p N H
  have Hpos : (0:ℝ)<H := by exact_mod_cast (show 0<H by omega)
  apply (mul_le_mul_iff_right₀ Hpos).mp
  calc
    _ = (H:ℝ)^2*‖∑ j ∈ range N, character (p j)‖^2 := by ring
    _ ≤ _ := base
    _ ≤ ((N+H-1:ℕ):ℝ)*((H:ℝ)*N+2*((H:ℝ)*((H:ℝ)*P+B*(1+Real.log H)))) := by
      exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left est (by norm_num))) (Nat.cast_nonneg _)
    _ = _ := by ring

end FactorialDifferencing
#print axioms FactorialDifferencing.exponential_differencing
#print axioms FactorialDifferencing.uniform_differencing
#print axioms FactorialDifferencing.differencing_with_inverse_lag
