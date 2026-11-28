import ReciprocalSpacing
import ReciprocalFirstDerivative
import Mathlib.Algebra.BigOperators.Intervals

/-! A finite second-derivative estimate for the reciprocal phase. The
single-strip Kusmin–Landau inequality and the count of exceptional
increments give the square-root bound, uniformly on each subinterval of
a factor-three interval and for every positive real frequency. -/

noncomputable section
open Finset ReciprocalFirstDerivative
namespace ReciprocalSpacing

/-- A reciprocal phase sum on every subinterval of [M,3M]. The parameter η
balances the total number of near-integer increments and the cost of
cancellation on the remaining intervals. -/
theorem reciprocal_block {Y η : ℝ} {M a b : ℕ} (hY : 0 < Y) (hM : 1 ≤ M)
    (ha : M ≤ a) (hb : b ≤ 3*M) (hη : 0 < η) (hη' : η ≤ 1) :
    ‖∑ j ∈ Icc a b, wave (Y/(j:ℝ))‖ ≤
      (Y/(M:ℝ)^2+η+1)*(1+2*η/step Y M + (1+1/η)) := by
  apply block_of_safe_cells hY hM ha hb hη hη' (by positivity) _ (by simp)
  intro c d ac cd db k band
  let f (j : ℕ) : ℝ := Y/((c+j:ℕ):ℝ)
  have diff (j : ℕ) : f (j+1)-f j = -gap Y (c+j) := by
    have e := phase_sub_phase (Y:=Y) (j:=c+j) (by omega)
    dsimp [f]
    push_cast at *
    rw [← add_assoc]
    linarith
  have inc (j : ℕ) (hj : j < d-c) : f (j+1)-f j ≤ f (j+2)-f (j+1) := by
    rw [diff j,diff (j+1),neg_le_neg_iff]
    have sep := separation hY.le hM (j:=c+j) (k:=c+(j+1)) (by omega) (by omega) (by omega)
    have nonneg : 0 ≤ ((c+(j+1):ℕ):ℝ)-((c+j:ℕ):ℝ) := sub_nonneg.mpr (by exact_mod_cast (show c+j ≤ c+(j+1) by omega))
    linarith [mul_nonneg nonneg (step_pos hY M).le]
  have safe (j : ℕ) (hj : j ≤ d-c) :
      ((-k-1:ℤ):ℝ)+η ≤ f (j+1)-f j ∧ f (j+1)-f j ≤ ((-k-1:ℤ):ℝ)+1-η := by
    have bj := band (c+j) (mem_Icc.mpr ⟨by omega,by omega⟩)
    rw [diff]
    push_cast
    constructor <;> linarith [bj.1,bj.2]
  have h := first_difference_bound f (d-c) (-k-1) hη safe inc
  rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range,show d+1-c = d-c+1 by omega]
  simpa only [f, Nat.add_comm] using h


/-- The classical square-root exponent-pair bound for every reciprocal
phase, with an explicit absolute constant on a factor-three interval. -/
theorem reciprocal_sqrt_bound {Y : ℝ} {M a b : ℕ} (hY : 0 < Y) (hM : 1 ≤ M)
    (ha : M ≤ a) (hb : b ≤ 3*M) :
    ‖∑ j ∈ Icc a b, wave (Y/(j:ℝ))‖ ≤
      335*(Real.sqrt (Y/M) + (M:ℝ)^2/Y) := by
  let m : ℝ := M
  have m1 : 1 ≤ m := by dsimp [m]; exact_mod_cast hM
  have mp : 0 < m := by linarith
  have wp : 0 < Real.sqrt (Y/m) := Real.sqrt_pos.mpr (div_pos hY mp)
  let W := Real.sqrt (Y/m)
  have ws : W^2*m=Y := by
    rw [show W^2=Y/m from Real.sq_sqrt (div_nonneg hY.le mp.le),div_mul_cancel₀ _ mp.ne']
  change _ ≤ 335*(W+m^2/Y)
  have rp : 0 ≤ m^2/Y := by positivity
  by_cases ab : a ≤ b
  · have posA : 0 < (a:ℝ) := by exact_mod_cast (show 0<a by omega)
    have am : m ≤ a := by dsimp [m]; exact_mod_cast ha
    have bm : (b:ℝ) ≤ 3*m := by dsimp [m]; exact_mod_cast hb
    by_cases low : 2*Y ≤ m^2
    · have aa : m^2 ≤ (a:ℝ)*(a+1) := by rw [sq]; gcongr; linarith
      have h := reciprocal_low_frequency (b-a) posA hY (low.trans aa)
      have castN : ((b-a:ℕ):ℝ) = (b:ℝ)-a := Nat.cast_sub ab
      rw [castN,show (a:ℝ)+(b-a)=b by ring] at h
      rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range,show b+1-a = b-a+1 by omega]
      simp only [Nat.cast_add] 
      apply h.trans
      have prod : (b:ℝ)*(b+1) ≤ 12*m^2 := by
        calc _ ≤ (3*m)*(4*m) := mul_le_mul bm (by linarith) (by positivity) (by positivity)
             _ = _ := by ring
      have one : 1 ≤ m^2/Y := (le_div_iff₀ hY).mpr (by linarith)
      have hh := div_le_div_of_nonneg_right prod hY.le
      rw [show 12*m^2/Y=12*(m^2/Y) by ring] at hh
      linarith [show 0≤W from wp.le]
    · by_cases high : m^3 ≤ Y
      · have ms : m ≤ W := by
          by_contra! eq
          have q := mul_lt_mul_of_pos_right (pow_lt_pow_left₀ eq wp.le (by decide : 2≠0)) mp
          nlinarith
        have len : ((Icc a b).card:ℝ) ≤ 3*m := by
          rw [Nat.card_Icc]
          dsimp only [m]
          exact_mod_cast (show b+1-a ≤3*M by omega)
        calc _ ≤ ∑ j ∈ Icc a b,‖wave (Y/(j:ℝ))‖ := norm_sum_le _ _
             _ = (Icc a b).card := by simp
             _ ≤ 3*m := len
             _ ≤ _ := by linarith
      · let η := W/m
        have ep : 0 < η := div_pos wp mp
        have es : η ≤ 1 := by
          apply (div_le_one mp).mpr
          by_contra! e
          have q := mul_lt_mul_of_pos_right (pow_lt_pow_left₀ e mp.le (by decide : 2≠0)) mp
          nlinarith
        have ee : η^2* m^3 = Y := by
          dsimp only [η]
          rw [← ws]
          field_simp
        have raw := reciprocal_block hY hM ha hb ep es
        have c₁ : Y/m^2+η+1 ≤ 5*(Y/m^2) := by
          have z : (1:ℝ)/2 ≤ Y/m^2 := (le_div_iff₀ (sq_pos_of_pos mp)).mpr (by linarith)
          linarith
        have cap : (3*m+1)^3 ≤ 64*m^3 := by
          calc _ ≤ (4*m)^3 := by gcongr; linarith
               _ = _ := by ring
        have hterm : 2*η/step Y M ≤ 64/η := by
          change 2*η/(2*Y/(3*m+1)^3) ≤ 64/η
          have pp : (0:ℝ)<3*m+1 := by positivity
          field_simp
          nlinarith [mul_le_mul_of_nonneg_left cap (sq_nonneg η)]
        have c₂ : 1+2*η/step Y M+(1+1/η) ≤ 67/η := by
          have one : 1 ≤ 1/η := (one_le_div ep).mpr es
          linarith [show (67:ℝ)/η=1/η+2*(1/η)+64/η by ring]
        have non := step_pos hY M
        have est := mul_le_mul c₁ c₂ (by positivity) (by positivity)
        apply raw.trans (est.trans ?_)
        have alg : 5*(Y/m^2)*(67/η) = 335*W := by
          dsimp only [η]
          rw [← ws]
          field_simp
          ring
        rw [alg]
        linarith
  · rw [Icc_eq_empty ab,sum_empty,norm_zero]
    positivity

end ReciprocalSpacing
#print axioms ReciprocalSpacing.reciprocal_block
#print axioms ReciprocalSpacing.reciprocal_sqrt_bound
