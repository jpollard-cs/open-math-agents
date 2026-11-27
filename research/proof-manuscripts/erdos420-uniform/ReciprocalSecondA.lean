import ReciprocalAOptimization
import ReciprocalShiftedFirstA

/-! A second van der Corput differencing step for reciprocal exponential sums,
giving the concrete (1/14,11/14) exponent pair with an absolute constant. -/

noncomputable section
open Finset Real ReciprocalFirstDerivative
namespace FactorialReciprocal

/-- Uniform (1/14,11/14) estimate for a reciprocal phase on a real-base
block. The length N can be zero and is bounded by 2B+1. -/
theorem reciprocal_second_A {B Y : ℝ} (N : ℕ) (hB : 1 ≤ B) (hY : 0 < Y)
    (len : (N:ℝ) ≤ 2*B+1) :
    ‖∑ j ∈ range N, wave (Y/(B+j))‖ ≤
      80000000*(B^(11/14:ℝ)*(Y/B^2)^(1/14:ℝ)+B^2/Y) := by
  let X := Y/B^2
  let p (j : ℕ) := Y/(B+j)
  have bp : 0 < B := by linarith
  have xp : 0 < X := by dsimp [X]; positivity
  have inv : 1/X = B^2/Y := by dsimp [X]; rw [one_div_div]
  have previous : ‖∑ j ∈ range N, FactorialDifferencing.character (p j)‖ ≤
      10000000*(B^(2/3:ℝ)*X^(1/6:ℝ)+1/X) := by
    simp only [character_eq_wave,p]
    apply (reciprocal_first_A N hB hY len).trans
    rw [inv]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have each (d : ℕ) (hd : 1 ≤ d) (dh : (d:ℝ) ≤ B) :
      ‖∑ j ∈ range (N-d), FactorialDifferencing.character (p (j+d)-p j)‖ ≤
      10000000*(B^(1/2:ℝ)*((d:ℝ)*X)^(1/6:ℝ)+B/((d:ℝ)*X)) := by
    have dp : 0 < (d:ℝ) := by exact_mod_cast (show 0<d by omega)
    have wp : 0 < (d:ℝ)*X := mul_pos dp xp
    have len' : ((N-d:ℕ):ℝ) ≤ 2*B+1 :=
      (show ((N-d:ℕ):ℝ) ≤ (N:ℝ) by exact_mod_cast Nat.sub_le N d).trans len
    have raw := shifted_first_A [(d:ℝ)] (N-d) hB hY (by simpa using dp) (by simpa using dh) len'
    have phase (j : ℕ) : FactorialDifferencing.character (p (j+d)-p j) =
        star (wave (Y*diffPow [(d:ℝ)] 1 (B+j))) := by
      rw [character_eq_wave,← wave_neg_eq_star]
      congr 1
      dsimp [p,diffPow]
      push_cast
      simp only [pow_one,div_eq_mul_inv,add_assoc]
      ring
    simp_rw [phase]
    rw [← star_sum, norm_star]
    apply raw.trans
    have slope : effectiveSlope [(d:ℝ)] Y B = 2*((d:ℝ)*X)/B := by
      rw [effectiveSlope_cons [] _ bp]
      norm_num [effectiveSlope,X]
      ring
    rw [slope]
    have c2 : (2:ℝ)^(1/6:ℝ) ≤ 2 := by
      simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
        (by norm_num : (1/6:ℝ) ≤ 1)
    have power : B^(2/3:ℝ)*(2*((d:ℝ)*X)/B)^(1/6:ℝ) =
        (2:ℝ)^(1/6:ℝ)*(B^(1/2:ℝ)*((d:ℝ)*X)^(1/6:ℝ)) := by
      have wp' : 0 < 2*((d:ℝ)*X) := by positivity
      have up : 0 < 2*((d:ℝ)*X)/B := div_pos wp' bp
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
      rw [Real.log_mul (rpow_pos_of_pos bp _).ne' (rpow_pos_of_pos up _).ne',
        Real.log_mul (rpow_pos_of_pos (by norm_num : (0:ℝ)<2) _).ne' (by positivity),
        Real.log_mul (rpow_pos_of_pos bp _).ne' (rpow_pos_of_pos wp _).ne',
        Real.log_rpow bp,Real.log_rpow bp,Real.log_rpow up,
        Real.log_rpow (by norm_num : (0:ℝ)<2),Real.log_rpow wp,
        Real.log_div wp'.ne' bp.ne',Real.log_mul (by norm_num : (2:ℝ)≠0) wp.ne']
      ring
    have denom : 1/(2*((d:ℝ)*X)/B) ≤ B/((d:ℝ)*X) := by
      rw [one_div_div]
      exact div_le_div_of_nonneg_left bp.le wp (by linarith)
    let V := B^(1/2:ℝ)*((d:ℝ)*X)^(1/6:ℝ)
    let W := B/((d:ℝ)*X)
    have vp : 0 ≤ V := by dsimp [V]; positivity
    have w0 : 0 ≤ W := by dsimp [W]; positivity
    rw [power]
    change 8*firstAWeight [(d:ℝ)]*((2:ℝ)^(1/6:ℝ)*V+1/(2*((d:ℝ)*X)/B)) ≤ 10000000*(V+W)
    have coeff : 8*firstAWeight [(d:ℝ)] = 4665600 := by norm_num [firstAWeight]
    rw [coeff]
    calc _ ≤ 4665600*(2*V+W) := mul_le_mul_of_nonneg_left
            (add_le_add (mul_le_mul_of_nonneg_right c2 vp) denom) (by norm_num)
         _ ≤ _ := by linarith
  have result := FactorialDifferencing.second_A_of_differences p hB xp
    (by norm_num : (1:ℝ) ≤ 10000000) (by linarith : (N:ℝ) ≤ 3*B) previous each
  rw [inv] at result
  norm_num only [show (8:ℝ)*10000000=80000000 by norm_num] at result
  simpa only [p,X,character_eq_wave] using result

/-- The natural-endpoint version used when reindexing multiples in the
sawtooth Fourier sums. The endpoints may define an empty interval. -/
theorem reciprocal_second_A_Icc {M b : ℕ} {Y : ℝ} (hm : 1 ≤ M) (hy : 0 < Y)
    (hb : b ≤ 3*M) :
    ‖∑ q ∈ Icc M b, wave (Y/(q:ℝ))‖ ≤
      80000000*((M:ℝ)^(11/14:ℝ)*(Y/(M:ℝ)^2)^(1/14:ℝ)+(M:ℝ)^2/Y) := by
  have le : b+1-M ≤ 2*M+1 := by omega
  have bound := reciprocal_second_A (b+1-M) (by exact_mod_cast hm : (1:ℝ) ≤ M) hy
    (by exact_mod_cast le)
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simpa only [Nat.cast_add] using bound

end FactorialReciprocal
#print axioms FactorialReciprocal.reciprocal_second_A
#print axioms FactorialReciprocal.reciprocal_second_A_Icc
