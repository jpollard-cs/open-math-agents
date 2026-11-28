import ReciprocalShiftedSquareRoot
import ReciprocalFirstA

/-! An actual reciprocal exponential sum, after any fixed number of shifts,
satisfies the exponent-pair estimate (1/6, 2/3). The inverse-frequency cost
retains every shift. -/
noncomputable section
open Finset Real ReciprocalFirstDerivative
open scoped ComplexConjugate
namespace FactorialReciprocal

/-- Effective first-difference size for a reciprocal phase with shifts. -/
def effectiveSlope (hs : List ℝ) (C B : ℝ) : ℝ :=
  (C*((hs.length+1).factorial : ℝ)*hs.prod)/B^(hs.length+2)

def firstAWeight (hs : List ℝ) : ℝ :=
  25*(6:ℝ)^(hs.length+4)*((hs.length:ℝ)+2)

theorem character_eq_wave (x : ℝ) : FactorialDifferencing.character x = wave x := by
  unfold FactorialDifferencing.character wave
  congr 1
  push_cast
  ring

theorem wave_neg_eq_star (x : ℝ) : wave (-x) = star (wave x) := by
  unfold wave
  change _ = conj _
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul,Complex.ofReal_neg,Complex.conj_ofReal,Complex.conj_I,map_ofNat]
  ring

theorem effectiveSlope_cons {B C : ℝ} (hs : List ℝ) (d : ℝ) (hB : 0 < B) :
    effectiveSlope (d::hs) C B = ((hs.length:ℝ)+2)*d*effectiveSlope hs C B/B := by
  dsimp [effectiveSlope]
  rw [Nat.factorial_succ (hs.length+1),show hs.length+1+2=hs.length+2+1 by omega,
      pow_succ B (hs.length+2)]
  push_cast
  field_simp
  ring

private lemma sqrt_range (hs : List ℝ) (N : ℕ) {C B : ℝ} (hB : 1 ≤ B)
    (hC : 0 < C) (pos : ∀ t ∈ hs, 0 < t) (sum : hs.sum ≤ 2*B) (len : (N:ℝ) ≤ 2*B+1) :
    ‖∑ j ∈ range N, wave (C*diffPow hs 1 (B+j))‖ ≤
      25*(6:ℝ)^(hs.length+3)*(sqrt (B*effectiveSlope hs C B)+1/effectiveSlope hs C B) := by
  have bp : 0 < B := by linarith
  have xp : 0 < effectiveSlope hs C B := by
    have ph := List.prod_pos pos
    dsimp [effectiveSlope]; positivity
  cases N with
  | zero => simp only [range_zero,sum_empty,norm_zero]; positivity
  | succ n =>
    rw [Nat.range_succ_eq_Icc_zero]
    exact shifted_sqrt_bound_two hs n 0 n hB hC pos sum (by push_cast at len; linarith) le_rfl

/-- The first A-process estimate for any mixed difference of the reciprocal.
For each additional differencing lag d≤B the total shift in the square-root
estimate is at most 2B. -/
theorem shifted_first_A (hs : List ℝ) (N : ℕ) {C B : ℝ} (hB : 1 ≤ B)
    (hC : 0 < C) (pos : ∀ t ∈ hs, 0 < t) (sum : hs.sum ≤ B)
    (len : (N:ℝ) ≤ 2*B+1) :
    ‖∑ j ∈ range N, wave (C*diffPow hs 1 (B+j))‖ ≤
      8*firstAWeight hs*(B^(2/3:ℝ)*(effectiveSlope hs C B)^(1/6:ℝ)+1/effectiveSlope hs C B) := by
  let X := effectiveSlope hs C B
  let U := (hs.length:ℝ)+2
  let L := 25*(6:ℝ)^(hs.length+4)
  have bp : 0 < B := by linarith
  have xp : 0<X := by
    have ph := List.prod_pos pos
    dsimp [X,effectiveSlope]; positivity
  have up : 1 ≤ U := by dsimp [U]; linarith [Nat.cast_nonneg (α:=ℝ) hs.length]
  have lp : 1 ≤ L := by
    have h : 1≤(6:ℝ)^(hs.length+4) := one_le_pow₀ (by norm_num)
    dsimp [L]; linarith
  have weight_eq : firstAWeight hs = L*U := rfl
  have kp : 1 ≤ firstAWeight hs := weight_eq ▸ one_le_mul_of_one_le_of_one_le lp up
  let p (j : ℕ) := C*diffPow hs 1 (B+j)
  have base : ‖∑ j ∈ range N, FactorialDifferencing.character (p j)‖ ≤
      firstAWeight hs*(sqrt (B*X)+1/X) := by
    simp only [character_eq_wave,p]
    apply (sqrt_range hs N hB hC pos (by linarith) len).trans
    apply mul_le_mul_of_nonneg_right _ (by positivity : 0 ≤ sqrt (B*X)+1/X)
    have inc : (6:ℝ)^(hs.length+3) ≤ 6^(hs.length+4) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have lku : L ≤ L*U := by simpa using mul_le_mul_of_nonneg_left up (by linarith : 0 ≤ L)
    rw [weight_eq]
    exact (mul_le_mul_of_nonneg_left inc (by norm_num)).trans lku
  have shifts (d : ℕ) (hd : 0<d) (dh : (d:ℝ) ≤ B) :
      ‖∑ j ∈ range (N-d), FactorialDifferencing.character (p (j+d)-p j)‖ ≤
      firstAWeight hs*(sqrt ((d:ℝ)*X)+B/((d:ℝ)*X)) := by
    have dp : 0 < (d:ℝ) := by exact_mod_cast hd
    have xp' : 0 < (d:ℝ)*X := mul_pos dp xp
    have pos' : ∀ t ∈ (d:ℝ)::hs, 0<t := by
      intro t ht; rcases List.mem_cons.mp ht with rfl|h
      · exact dp
      · exact pos _ h
    have sz : ((N-d:ℕ):ℝ) ≤ 2*B+1 :=
      (show ((N-d:ℕ):ℝ) ≤ N by exact_mod_cast Nat.sub_le N d).trans len
    have orig := sqrt_range ((d:ℝ)::hs) (N-d) hB hC pos' (by simp; linarith) sz
    have phase (j : ℕ) : FactorialDifferencing.character (p (j+d)-p j) =
        star (wave (C*diffPow ((d:ℝ)::hs) 1 (B+j))) := by
      rw [character_eq_wave,← wave_neg_eq_star]
      congr 1
      dsimp [p,diffPow]
      push_cast
      rw [← add_assoc]; ring
    simp_rw [phase]
    rw [←star_sum,norm_star]
    apply orig.trans
    have eq : effectiveSlope ((d:ℝ)::hs) C B = U*((d:ℝ)*X)/B := by
      rw [effectiveSlope_cons hs _ bp]; dsimp [X,U]; ring
    rw [eq]
    have baseEq : B*(U*((d:ℝ)*X)/B)=U*((d:ℝ)*X) := by field_simp
    have su : sqrt U ≤ U := (Real.sqrt_le_iff).mpr
      ⟨by linarith,by nlinarith [mul_nonneg (sub_nonneg.mpr up) (by linarith : 0≤U)]⟩
    have rt : sqrt (B*(U*((d:ℝ)*X)/B)) ≤ U*sqrt ((d:ℝ)*X) := by
      rw [baseEq,Real.sqrt_mul (by linarith : 0≤U)]
      exact mul_le_mul_of_nonneg_right su (Real.sqrt_nonneg _)
    have denom : (d:ℝ)*X ≤ U*((d:ℝ)*X) := by simpa using mul_le_mul_of_nonneg_right up xp'.le
    have inv : 1/(U*((d:ℝ)*X)/B) ≤ U*(B/((d:ℝ)*X)) := by
      rw [one_div_div]
      apply (div_le_div_of_nonneg_left bp.le xp' denom).trans
      simpa using mul_le_mul_of_nonneg_right up (div_nonneg bp.le xp'.le)
    change L*(sqrt (B*(U*((d:ℝ)*X)/B))+1/(U*((d:ℝ)*X)/B)) ≤ _
    calc _ ≤ L*(U*sqrt ((d:ℝ)*X)+U*(B/((d:ℝ)*X))) :=
           mul_le_mul_of_nonneg_left (add_le_add rt inv) (by linarith)
         _ = _ := by rw [weight_eq]; ring
  have raw := ReciprocalAProcess.first_A_character p N hB xp kp (by linarith) base shifts
  simpa only [character_eq_wave,p,X] using raw

/-- The first A-process exponent pair for the unshifted reciprocal with an
explicit absolute constant. B may be real, and the length is an integer. -/
theorem reciprocal_first_A {B Y : ℝ} (N : ℕ) (hB : 1 ≤ B) (hY : 0 < Y)
    (len : (N:ℝ) ≤ 2*B+1) :
    ‖∑ j ∈ range N, wave (Y/(B+j))‖ ≤
      518400*(B^(2/3:ℝ)*(Y/B^2)^(1/6:ℝ)+B^2/Y) := by
  have h := shifted_first_A [] N hB hY (by simp) (by simp; linarith) len
  norm_num [diffPow,effectiveSlope,firstAWeight,div_eq_mul_inv] at h ⊢
  exact h

/-- Natural endpoints for reindexing a sieve sum, including empty blocks. -/
theorem reciprocal_first_A_Icc {M b : ℕ} {Y : ℝ} (hm : 1 ≤ M) (hy : 0 < Y)
    (hb : b ≤ 3*M) :
    ‖∑ q ∈ Icc M b, wave (Y/(q:ℝ))‖ ≤
      518400*((M:ℝ)^(2/3:ℝ)*(Y/(M:ℝ)^2)^(1/6:ℝ)+(M:ℝ)^2/Y) := by
  have len : b+1-M ≤ 2*M+1 := by omega
  have bound := reciprocal_first_A (b+1-M) (by exact_mod_cast hm : (1:ℝ)≤M) hy
    (by exact_mod_cast len)
  rw [← Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simpa only [Nat.cast_add] using bound

end FactorialReciprocal
#print axioms FactorialReciprocal.shifted_first_A
#print axioms FactorialReciprocal.reciprocal_first_A
#print axioms FactorialReciprocal.reciprocal_first_A_Icc
