import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! A discrete first-derivative estimate for phases with increasing increments
in a single interval between integers. The proof uses the telescoping
cotangent multiplier, as in the Kusmin–Landau inequality. -/

noncomputable section
open Finset Complex
namespace ReciprocalFirstDerivative

/-- The unit character on the real line, with period one. -/
def wave (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * (2 * (Real.pi : ℂ) * I))

theorem wave_add (x y : ℝ) : wave (x+y) = wave x * wave y := by
  simp [wave, add_mul, Complex.exp_add]

theorem wave_int (k : ℤ) : wave (k : ℝ) = 1 := by
  simp [wave, Complex.exp_int_mul_two_pi_mul_I]

@[simp] theorem norm_wave (x : ℝ) : ‖wave x‖ = 1 := by
  convert Complex.norm_exp_ofReal_mul_I (x*(2*Real.pi)) using 2
  simp [wave, mul_assoc]

private lemma wave_ne_one {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    wave x ≠ 1 := by
  intro h
  obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have c : (2 * (Real.pi : ℂ) * I) ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) hpi) I_ne_zero
  have eq : (x : ℂ) = (k : ℂ) := mul_right_cancel₀ c hk
  have eqr : x = (k : ℝ) := by exact_mod_cast eq
  rw [eqr] at hx hx'
  have hk0 : 0 < k := by exact_mod_cast hx
  have hk1 : k < 1 := by exact_mod_cast hx'
  omega

private def phaseCot (x : ℝ) := Real.cot (Real.pi*x)
private def multiplier (x : ℝ) : ℂ := (1 + I*(phaseCot x : ℂ))/2

private lemma multiplier_identity {x : ℝ} (hx : 0 < x) (hx' : x < 1) :
    (1-wave x)*multiplier x = 1 := by
  have hz := sub_ne_zero.mpr (wave_ne_one hx hx').symm
  have rat := Complex.cot_pi_eq_exp_ratio (x : ℂ)
  have hh : (phaseCot x : ℂ) = (wave x+1)/(I*(1-wave x)) := by
    simpa [phaseCot,Complex.ofReal_cot,Complex.ofReal_mul,wave,mul_comm,mul_left_comm,mul_assoc] using rat
  unfold multiplier
  rw [hh]
  field_simp
  ring

private lemma phaseCot_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    phaseCot b ≤ phaseCot a := by
  have sa : 0 < Real.sin (Real.pi*a) := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ha)
    (by nlinarith [Real.pi_pos,mul_pos Real.pi_pos (by linarith : 0 < 1-a)])
  have sb : 0 < Real.sin (Real.pi*b) := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos (ha.trans_le hab))
    (by nlinarith [Real.pi_pos,mul_pos Real.pi_pos (sub_pos.mpr hb)])
  have ap : 0 ≤ Real.pi*a := mul_nonneg Real.pi_pos.le ha.le
  have bp : Real.pi*b ≤ Real.pi := by simpa using mul_le_mul_of_nonneg_left hb.le Real.pi_pos.le
  have h := Real.sin_nonneg_of_nonneg_of_le_pi
    (show 0 ≤ Real.pi*b-Real.pi*a by nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hab)])
    (show Real.pi*b-Real.pi*a ≤ Real.pi by linarith)
  rw [Real.sin_sub] at h
  unfold phaseCot
  rw [Real.cot_eq_cos_div_sin,Real.cot_eq_cos_div_sin,div_le_div_iff₀ sb sa]
  linarith

private lemma phaseCot_bound {a δ : ℝ} (hδ : 0 < δ) (ha : δ ≤ a) (hb : a ≤ 1-δ) :
    |phaseCot a| ≤ 1/(2*δ) := by
  have halfsin (y : ℝ) (hy : 0 ≤ y) (hy' : y ≤ 1/2) : 2*y ≤ Real.sin (Real.pi*y) := by
    convert Real.le_sin_mul (x := 2*y) (by positivity) (by linarith) using 2
    ring
  have sinlo : 2*δ ≤ Real.sin (Real.pi*a) := by
    by_cases hl : a ≤ 1/2
    · linarith [halfsin a (hδ.le.trans ha) hl]
    · have h := halfsin (1-a) (by linarith) (by linarith)
      rw [show Real.pi*(1-a) = Real.pi-Real.pi*a by ring, Real.sin_pi_sub] at h
      linarith
  have hs : 0 < Real.sin (Real.pi*a) := by linarith
  rw [phaseCot,Real.cot_eq_cos_div_sin,abs_div,abs_of_pos hs]
  exact div_le_div₀ (by norm_num) (abs_le.mpr ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩)
    (by positivity) sinlo

private lemma norm_multiplier (a : ℝ) : ‖multiplier a‖ ≤ (1+|phaseCot a|)/2 := by
  have h := norm_add_le (1 : ℂ) (I*(phaseCot a : ℂ))
  simpa [multiplier,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs] using
    (div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2))

private lemma norm_multiplier_sub {a b : ℝ} (hc : phaseCot b ≤ phaseCot a) :
    ‖multiplier b - multiplier a‖ = (phaseCot a-phaseCot b)/2 := by
  have eq : multiplier b - multiplier a = I*((phaseCot b - phaseCot a : ℝ) : ℂ)/2 := by
    simp [multiplier]; ring
  rw [eq,norm_div,norm_mul,Complex.norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonpos (sub_nonpos.mpr hc)]
  simp

/-- Kusmin–Landau estimate for a block of unit phases. Only the increments
through the last term of the block are used. -/
theorem kusmin_landau {N : ℕ} (z : ℕ → ℂ) (a : ℕ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (unit : ∀ j ≤ N+1, ‖z j‖ = 1)
    (step : ∀ j ≤ N, z (j+1) = z j * wave (a j))
    (band : ∀ j ≤ N, δ ≤ a j ∧ a j ≤ 1-δ)
    (inc : ∀ j < N, a j ≤ a (j+1)) :
    ‖∑ j ∈ range (N+1), z j‖ ≤ 1 + 1/δ := by
  let M (j : ℕ) := multiplier (a j)
  have edge (j : ℕ) (hj : j ≤ N) : (z j-z (j+1))*M j = z j := by
    rw [step j hj, ← mul_one_sub]
    dsimp only [M]
    rw [mul_assoc,multiplier_identity (hδ.trans_le (band j hj).1) (by linarith [(band j hj).2]),mul_one]
  let E (j : ℕ) := (∑ i ∈ range (j+1), z i) - z 0*M 0 + z (j+1)*M j
  have err (j : ℕ) (hj : j ≤ N) : ‖E j‖ ≤ (phaseCot (a 0)-phaseCot (a j))/2 := by
    induction j with
    | zero =>
      have h := edge 0 (by omega)
      have eq : E 0 = 0 := by
        simp only [E, zero_add, sum_range_one]
        linear_combination -h
      simp [eq]
    | succ j ih =>
      have cp := phaseCot_antitone (hδ.trans_le (band j (by omega)).1) (inc j (by omega))
        (by linarith [(band (j+1) hj).2])
      have eq : E (j+1) = E j + z (j+1)*(M (j+1)-M j) := by
        dsimp only [E]
        rw [sum_range_succ (n := j+1)]
        linear_combination -(edge (j+1) hj)
      rw [eq]
      apply (norm_add_le ..).trans
      rw [norm_mul,unit (j+1) (by omega),one_mul,show M (j+1)-M j =
        multiplier (a (j+1))-multiplier (a j) from rfl,norm_multiplier_sub cp]
      linarith [ih (by omega)]
  have end_eq : (∑ j ∈ range (N+1), z j) = E N + z 0*M 0 - z (N+1)*M N := by
    dsimp only [E]; ring
  rw [end_eq]
  apply (norm_sub_le ..).trans
  apply (add_le_add (norm_add_le ..) le_rfl).trans
  rw [norm_mul,norm_mul,unit 0 (by omega),unit (N+1) (by omega),one_mul,one_mul]
  have b0 := phaseCot_bound hδ (band 0 (by omega)).1 (band 0 (by omega)).2
  have bN := phaseCot_bound hδ (band N le_rfl).1 (band N le_rfl).2
  have m0 : ‖M 0‖ ≤ (1+|phaseCot (a 0)|)/2 := norm_multiplier _
  have mN : ‖M N‖ ≤ (1+|phaseCot (a N)|)/2 := norm_multiplier _
  have den : 2*(1/(2*δ)) = 1/δ := by field_simp
  linarith [err N le_rfl, le_abs_self (phaseCot (a 0)), neg_le_abs (phaseCot (a N))]

/-- Real-phase form. The successive first differences are nondecreasing
and remain at distance at least δ from the ends of one unit interval. -/
theorem first_difference_bound (f : ℕ → ℝ) (N : ℕ) (k : ℤ) {δ : ℝ} (hδ : 0 < δ)
    (band : ∀ j ≤ N, (k:ℝ)+δ ≤ f (j+1)-f j ∧ f (j+1)-f j ≤ (k:ℝ)+1-δ)
    (inc : ∀ j < N, f (j+1)-f j ≤ f (j+2)-f (j+1)) :
    ‖∑ j ∈ range (N+1), wave (f j)‖ ≤ 1 + 1/δ := by
  let a (j : ℕ) := f (j+1)-f j-(k:ℝ)
  apply kusmin_landau (fun j => wave (f j)) a hδ (by simp)
  · intro j _
    have eq : f (j+1) = f j + (a j+(k:ℝ)) := by dsimp [a]; ring
    rw [eq,wave_add,wave_add,wave_int,mul_one]
  · intro j hj
    dsimp [a]; constructor <;> linarith [(band j hj).1,(band j hj).2]
  · intro j hj
    dsimp [a]
    linarith [inc j hj]


/-- For small frequencies the reciprocal phase stays in a single
nonresonant strip. This yields the inverse-frequency term directly. -/
theorem reciprocal_low_frequency {B Y : ℝ} (N : ℕ) (hB : 0 < B) (hY : 0 < Y)
    (small : 2*Y ≤ B*(B+1)) :
    ‖∑ j ∈ range (N+1), wave (Y/(B+j))‖ ≤ 1 + (B+N)*(B+N+1)/Y := by
  let den (j : ℕ) : ℝ := (B+j)*(B+j+1)
  have pos (j : ℕ) : 0 < den j := by dsimp [den]; positivity
  have mon : Monotone den := by
    intro a b hab
    dsimp [den]
    have habR : (a:ℝ) ≤ b := by exact_mod_cast hab
    gcongr
  have diff (j : ℕ) : Y/(B+(j+1 : ℕ))-Y/(B+j) = -(Y/den j) := by
    dsimp [den]
    push_cast
    have p : (B+(j:ℝ)) ≠ 0 := by positivity
    have q : (B+(j:ℝ)+1) ≠ 0 := by positivity
    rw [← add_assoc]
    field_simp
    ring
  let δ := Y/den N
  have hd : 0 < δ := div_pos hY (pos _)
  have hl (j : ℕ) : Y/den j ≤ 1/2 := by
    apply (div_le_iff₀ (pos j)).mpr
    have z : den 0 = B*(B+1) := by simp [den]
    linarith [mon (Nat.zero_le j)]
  have up (j : ℕ) (hj : j ≤ N) : δ ≤ Y/den j :=
    div_le_div_of_nonneg_left hY.le (pos j) (mon hj)
  have raw := first_difference_bound (fun j => Y/(B+j)) N (-1) hd (by
    intro j hj
    rw [diff]
    norm_num
    constructor
    · linarith [hl j,hl N,show δ=Y/den N by rfl]
    · linarith [up j hj]) (by
    intro j hj
    rw [diff j,diff (j+1),neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hY.le (pos j) (mon (Nat.le_succ j)))
  convert raw using 2
  dsimp [δ,den]
  field_simp

end ReciprocalFirstDerivative
#print axioms ReciprocalFirstDerivative.first_difference_bound
#print axioms ReciprocalFirstDerivative.reciprocal_low_frequency
