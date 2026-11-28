import ReciprocalShiftedBlocks
import ReciprocalShiftedSums
import Mathlib.Algebra.BigOperators.Intervals

/-! The square-root exponent pair for reciprocal phases and every
iterated shift of total size at most the base point. -/
noncomputable section
open Finset ReciprocalFirstDerivative
namespace FactorialReciprocal

/-- A square-root estimate on all subintervals, uniform in the scale and shifts.
The displayed constant depends only on the number of differencing steps. -/
theorem shifted_sqrt_of_span (hs : List ℝ) (N a b : ℕ) {C B D : ℝ} (hB : 1 ≤ B)
    (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) (hD : 1 ≤ D) (span : B+(N:ℝ)+1+hs.sum ≤ D*B)
    (hN : (N:ℝ) ≤ 2*B) (hb : b ≤ N) :
    let A := (C*((hs.length+1).factorial : ℝ)*hs.prod) / B^(hs.length+2)
    ‖∑ j ∈ Icc a b,wave (C*diffPow hs 1 (B+j))‖ ≤
      25*D^(hs.length+3)*(Real.sqrt (B*A)+1/A) := by
  let Q := C*((hs.length+1).factorial : ℝ)*hs.prod
  let k := hs.length+2
  let A := Q/B^k
  let K := D^(k+1)
  have bp : 0 < B := by linarith
  have hprod := List.prod_pos hn
  have hnn : ∀ t ∈ hs, 0 ≤ t := fun t ht => (hn t ht).le
  have sn := List.sum_nonneg hnn
  have qp : 0 < Q := by dsimp [Q]; positivity
  have ap : 0 < A := by dsimp [A]; positivity
  have kp : 1 ≤ K := one_le_pow₀ hD
  have kd : 0 < K := by linarith
  have pd : 0 < D := by linarith
  have ss := Real.sqrt_nonneg (B*A)
  have inv : 0 < 1/A := by positivity
  have qA : A*B^k=Q := div_mul_cancel₀ _ (pow_pos bp _).ne'
  change _ ≤ 25*K*(Real.sqrt (B*A)+1/A)
  by_cases ab : a ≤ b
  · have ar : (a:ℝ) ≤ b := by exact_mod_cast ab
    have br : (b:ℝ) ≤ N := by exact_mod_cast hb
    by_cases low : A < 1/2
    · have ba : 0 < B+a := by positivity
      have base : B^k ≤ (B+a)^k := pow_le_pow_left₀ bp.le (by linarith [Nat.cast_nonneg (α:=ℝ) a]) _
      have small : 2*Q ≤ (B+a)^k := by
        have e := (div_lt_iff₀ (pow_pos bp k)).mp (show Q/B^k < 1/2 from low)
        linarith
      have h := shifted_low_frequency hs (b-a) ba hC.le hnn qp small
      have castD : ((b-a:ℕ):ℝ) = b-a := Nat.cast_sub ab
      rw [castD,show B+a+((b:ℝ)-a)=B+b by ring] at h
      have bound : (B+b+1+hs.sum)^k ≤ (D*B)^k :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      have fac : (D*B)^k/Q ≤ K/A := by
        rw [mul_pow, show K=D^k*D by dsimp [K]; rw [pow_succ]]
        apply (div_le_div_iff₀ qp ap).mpr
        have mult : D^k*B^k*A=D^k*Q := by rw [← qA]; ring
        rw [mult]
        have pos : 0 ≤ D^k*Q := by positivity
        nlinarith [mul_nonneg (sub_nonneg.mpr hD) pos]
      have hfrac := (div_le_div_of_nonneg_right bound qp.le).trans fac
      have ka : 1 ≤ K/A := (le_div_iff₀ ap).mpr (by linarith)
      rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range,show b+1-a=b-a+1 by omega]
      simp only [Nat.cast_add]
      have hs' : ‖∑ l ∈ range (b-a+1),wave (C * diffPow hs 1 (B + ((a:ℝ)+l)))‖ ≤ 1+K/A := by
        simpa only [add_assoc] using h.trans (add_le_add le_rfl hfrac)
      apply hs'.trans
      have kr := mul_nonneg (show 0≤K by linarith) ss
      rw [mul_add,show 25*K*(1/A)=25*(K/A) by ring]
      nlinarith
    · by_cases hi : B < A
      · have len : ((Icc a b).card:ℝ) ≤ 3*B := by
          have le : (Icc a b).card ≤ N+1 := by rw [Nat.card_Icc]; omega
          have eh : ((Icc a b).card : ℝ) ≤ (N:ℝ)+1 := by exact_mod_cast le
          linarith
        have root : B ≤ Real.sqrt (B*A) := by
          rw [Real.le_sqrt bp.le (mul_nonneg bp.le ap.le)]
          nlinarith [mul_nonneg bp.le (sub_nonneg.mpr hi.le)]
        calc _ ≤ ∑ j ∈ Icc a b, ‖wave (C*diffPow hs 1 (B+j))‖ := norm_sum_le _ _
             _ = (Icc a b).card := by simp
             _ ≤ 3*B := len
             _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right kp (add_nonneg ss inv.le)]
      · let P := shiftedProfile hs N bp hC hn
        have apEq : P.cap = A := rfl
        have curv : P.cap/(K*B) ≤ P.step := by
          have num : Q ≤ C*((hs.length+2).factorial : ℝ)*hs.prod := by
            apply mul_le_mul_of_nonneg_right _ hprod.le
            apply mul_le_mul_of_nonneg_left _ hC.le
            exact_mod_cast (Nat.factorial_le (show hs.length+1 ≤ hs.length+2 by omega))
          have w : 0 < B+N+1+hs.sum := by positivity
          rw [apEq]
          change A/(K*B) ≤ C*((hs.length+2).factorial : ℝ)*hs.prod / (B+N+1+hs.sum)^(k+1)
          calc _ = Q/(D*B)^(k+1) := by
                 dsimp [A,K]
                 rw [mul_pow, pow_succ B k]
                 field_simp
               _ ≤ _ := div_le_div_of_nonneg_right num (by positivity)
               _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos w _)
                         (pow_le_pow_left₀ w.le (by linarith) _)
        have h := shifted_middle_frequency hs N a b bp hC hn hb bp (show 0<K by linarith)
          (le_of_not_gt low) (le_of_not_gt hi) curv
        change _ ≤ 5*(3+2*K)*Real.sqrt (B*A) at h
        apply h.trans
        have c : 5*(3+2*K) ≤ 25*K := by linarith
        exact (mul_le_mul_of_nonneg_right c ss).trans
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right inv.le) (by positivity))
  · rw [Icc_eq_empty ab,sum_empty,norm_zero]
    positivity

theorem shifted_sqrt_bound (hs : List ℝ) (N a b : ℕ) {C B : ℝ} (hB : 1 ≤ B)
    (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) (hsum : hs.sum ≤ B)
    (hN : (N:ℝ) ≤ 2*B) (hb : b ≤ N) :
    let A := (C*((hs.length+1).factorial : ℝ)*hs.prod) / B^(hs.length+2)
    ‖∑ j ∈ Icc a b,wave (C*diffPow hs 1 (B+j))‖ ≤
      25*(5:ℝ)^(hs.length+3)*(Real.sqrt (B*A)+1/A) := by
  apply shifted_sqrt_of_span hs N a b hB hC hn (by norm_num : (1:ℝ) ≤ 5) (by linarith) hN hb

/-- Two arbitrary shifts of size at most B are covered by the larger span constant six. -/
theorem shifted_sqrt_bound_two (hs : List ℝ) (N a b : ℕ) {C B : ℝ} (hB : 1 ≤ B)
    (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) (hsum : hs.sum ≤ 2*B)
    (hN : (N:ℝ) ≤ 2*B) (hb : b ≤ N) :
    let A := (C*((hs.length+1).factorial : ℝ)*hs.prod) / B^(hs.length+2)
    ‖∑ j ∈ Icc a b,wave (C*diffPow hs 1 (B+j))‖ ≤
      25*(6:ℝ)^(hs.length+3)*(Real.sqrt (B*A)+1/A) := by
  apply shifted_sqrt_of_span hs N a b hB hC hn (by norm_num : (1:ℝ) ≤ 6) (by linarith) hN hb

end FactorialReciprocal
#print axioms FactorialReciprocal.shifted_sqrt_bound
#print axioms FactorialReciprocal.shifted_sqrt_bound_two
