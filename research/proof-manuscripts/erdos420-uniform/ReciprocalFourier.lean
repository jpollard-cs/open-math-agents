import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Finite Fourier coefficients of the centered sawtooth and a one-sided box on a cyclic grid. -/
noncomputable section
open Finset
namespace FactorialFourier

def sawCoeff (Q : ℕ) (w : ℂ) : ℂ :=
  ∑ m ∈ range Q, ((m : ℂ)/Q - 1/2) * w^m

def boxCoeff (L : ℕ) (w : ℂ) : ℂ :=
  (∑ m ∈ range L, w^m)/(L:ℂ)

private theorem weighted_geom (Q : ℕ) (w : ℂ) :
    (w-1)*(∑ m ∈ range Q, (m:ℂ)*w^m) =
      (Q:ℂ)*w^Q - w*(∑ m ∈ range Q, w^m) := by
  induction Q with
  | zero => simp
  | succ Q ih => rw [sum_range_succ,sum_range_succ,Nat.cast_succ,pow_succ,mul_add,ih]; ring

/-- Every nonconstant Fourier coefficient of the raw grid sawtooth. -/
theorem sawCoeff_eq {Q : ℕ} (hQ : 0<Q) {w : ℂ} (hw : w^Q=1) (hne : w≠1) :
    sawCoeff Q w = 1/(w-1) := by
  have g : ∑ m ∈ range Q, w^m = 0 := by
    have h := geom_sum_mul w Q
    rw [hw, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have q : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  have s := weighted_geom Q w
  rw [hw,g] at s
  have eq : sawCoeff Q w =
      (∑ m ∈ range Q, (m:ℂ)*w^m)/Q - (1/2)*(∑ m ∈ range Q, w^m) := by
    rw [sawCoeff, sum_div, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro m _; ring
  rw [eq,g,mul_zero,sub_zero]
  field_simp
  linear_combination s

/-- Taking absolute values termwise and using the geometric series give complementary bounds. -/
theorem boxCoeff_bound {L : ℕ} (hL : 0<L) {w : ℂ} (hn : ‖w‖=1) (hne : w≠1) :
    ‖boxCoeff L w‖ ≤ min 1 (2/((L:ℝ)*‖w-1‖)) := by
  have l : (0:ℝ)<L := by exact_mod_cast hL
  have d := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  rw [boxCoeff,norm_div,Complex.norm_natCast]
  apply le_min
  · apply (div_le_iff₀ l).mpr
    calc
      _ ≤ ∑ m ∈ range L, ‖w^m‖ := norm_sum_le _ _
      _ = _ := by simp [norm_pow,hn]
  · apply (le_div_iff₀ (mul_pos l d)).mpr
    rw [← mul_assoc,div_mul_cancel₀ _ l.ne',← norm_mul,geom_sum_mul]
    simpa [norm_pow,hn,one_add_one_eq_two] using norm_sub_le (w^L) 1

/-- The chord at phase x≥0 is bounded below in terms of its distance from either end of [0,1]. -/
theorem chord_lower (x : ℝ) (hx : 0≤x) (hx' : x≤1) :
    4*min x (1-x) ≤ ‖Complex.exp (Complex.I*(2*Real.pi*x : ℝ))-1‖ := by
  rw [Complex.norm_exp_I_mul_ofReal_sub_one,show 2*Real.pi*x/2 = Real.pi*x by ring]
  have hπ := Real.pi_pos
  have h := Real.sin_nonneg_of_nonneg_of_le_pi (mul_nonneg hπ.le hx)
    (by simpa using mul_le_mul_of_nonneg_left hx' hπ.le)
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg zero_le_two h)]
  rcases le_total x (1-x) with hhalf|hhalf
  · rw [min_eq_left hhalf]
    have hh := Real.le_sin_mul (x:=2*x) (by linarith) (by linarith)
    rw [show Real.pi/2*(2*x)=Real.pi*x by ring] at hh
    linarith
  · rw [min_eq_right hhalf]
    have hh := Real.le_sin_mul (x:=2*(1-x)) (by linarith) (by linarith)
    rw [show Real.pi/2*(2*(1-x))=Real.pi-Real.pi*x by ring,Real.sin_pi_sub] at hh
    linarith

variable {Q : ℕ} [NeZero Q]

/-- A centered sawtooth on residues represented by integers in [0,Q). -/
def gridSaw (a : ZMod Q) : ℂ := (a.val:ℂ)/(Q:ℂ)-1/2

theorem sum_grid {M : Type*} [AddCommMonoid M] (f : ZMod Q → M) :
    ∑ k, f k = ∑ m ∈ range Q, f (m : ZMod Q) := by
  apply sum_bij (fun k _ => k.val)
  · intro k _; exact mem_range.mpr k.val_lt
  · intro a _ b _ h; simpa using congrArg (fun m : ℕ => (m : ZMod Q)) h
  · intro m hm
    exact ⟨(m:ZMod Q),mem_univ _,ZMod.val_natCast_of_lt (mem_range.mp hm)⟩
  · intro k _; rw [ZMod.natCast_zmod_val]

theorem std_pow (a : ZMod Q) (m : ℕ) :
    ZMod.stdAddChar a ^ m = ZMod.stdAddChar ((m:ZMod Q)*a) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]

theorem std_ne_one {a : ZMod Q} (ha : a≠0) : ZMod.stdAddChar a ≠ 1 := by
  intro h
  apply ha
  apply ZMod.injective_stdAddChar
  simpa using h

theorem std_norm (a : ZMod Q) : ‖ZMod.stdAddChar a‖=1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem dft_gridSaw_as_sum (k : ZMod Q) :
    ZMod.dft (gridSaw (Q:=Q)) k = sawCoeff Q (ZMod.stdAddChar (-k)) := by
  rw [ZMod.dft_apply, sum_grid,sawCoeff]
  apply sum_congr rfl; intro m hm
  rw [smul_eq_mul,gridSaw,ZMod.val_natCast_of_lt (mem_range.mp hm),std_pow,mul_neg,mul_comm]

/-- The exact, unnormalized discrete Fourier transform at nonzero frequency. -/
theorem dft_gridSaw_eq {k : ZMod Q} (hk : k≠0) :
    ZMod.dft (gridSaw (Q:=Q)) k = 1/(ZMod.stdAddChar (-k)-1) := by
  rw [dft_gridSaw_as_sum]
  apply sawCoeff_eq (Nat.pos_of_ne_zero (NeZero.ne _)) _ (std_ne_one (neg_ne_zero.mpr hk))
  simp [std_pow]

theorem dft_gridSaw_zero : ZMod.dft (gridSaw (Q:=Q)) 0 = -(1/2) := by
  have h : (0:ℕ)<Q := Nat.pos_of_ne_zero (NeZero.ne _)
  have hz : (Q:ℂ)≠0 := by exact_mod_cast h.ne'
  have hsum : (∑ m ∈ range Q, (m:ℂ))*2=(Q:ℂ)*(Q-1) := by
    have v := sum_range_id_mul_two Q
    have hv := congrArg (Nat.cast : ℕ → ℂ) v
    simpa [Nat.cast_sub (show 1≤Q by omega)] using hv
  rw [dft_gridSaw_as_sum]
  simp only [sawCoeff,neg_zero,AddChar.map_zero_eq_one,one_pow,mul_one,sum_sub_distrib,← sum_div,
    sum_const,card_range,nsmul_eq_mul]
  field_simp
  linear_combination hsum

/-- Distance of a frequency to the nearest multiple of Q. -/
def folded (k : ZMod Q) : ℕ := min k.val (Q-k.val)

theorem folded_pos {k : ZMod Q} (hk : k≠0) : 0 < folded k := by
  exact lt_min (Nat.pos_of_ne_zero ((ZMod.val_ne_zero k).mpr hk)) (Nat.sub_pos_of_lt k.val_lt)

theorem folded_neg {k : ZMod Q} (hk : k≠0) : folded (-k)=folded k := by
  let : NeZero k := ⟨hk⟩
  simp [folded,ZMod.val_neg_of_ne_zero,Nat.sub_sub_self k.val_lt.le,min_comm]

theorem std_chord (k : ZMod Q) :
    4*(folded k:ℝ)/Q ≤ ‖ZMod.stdAddChar k-1‖ := by
  have qp : (0:ℝ)<Q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne Q))
  have vk : (k.val:ℝ)≤Q := by exact_mod_cast k.val_lt.le
  have x := chord_lower (k.val/Q) (by positivity) ((div_le_one qp).mpr vk)
  have hh : ZMod.stdAddChar k =
    Complex.exp (Complex.I*(2*Real.pi*((k.val:ℝ)/Q):ℝ)) := by
    have eq := ZMod.stdAddChar_coe (N:=Q) (k.val:ℤ)
    simp only [Int.cast_natCast,ZMod.natCast_zmod_val] at eq
    rw [eq]
    congr 1
    push_cast
    ring
  rw [hh,folded,Nat.cast_min,Nat.cast_sub k.val_lt.le]
  rw [show (1:ℝ)-k.val/Q=(Q-k.val)/Q by field_simp]
    at x
  rw [min_div_div_right qp.le] at x
  simpa only [mul_div_assoc] using x

/-- The normalized sawtooth coefficient is bounded by 1/(4 times the folded frequency). -/
theorem normalized_dft_bound {k : ZMod Q} (hk : k≠0) :
    ‖ZMod.dft (gridSaw (Q:=Q)) k‖ / Q ≤ 1/(4*(folded k:ℝ)) := by
  have p : (0:ℝ)<Q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne Q))
  have m : (0:ℝ)<folded k := by exact_mod_cast folded_pos hk
  have d := norm_pos_iff.mpr (sub_ne_zero.mpr (std_ne_one (neg_ne_zero.mpr hk)))
  have chord := std_chord (-k)
  rw [folded_neg hk] at chord
  have h := (div_le_iff₀ p).mp chord
  rw [dft_gridSaw_eq hk,norm_div,norm_one,div_div]
  exact one_div_le_one_div_of_le (by positivity) h

/-- The finite box multiplier decays inversely beyond frequency Q/L. -/
theorem box_frequency_bound {L : ℕ} (hL : 0<L) {k : ZMod Q} (hk : k≠0) :
    ‖boxCoeff L (ZMod.stdAddChar k)‖ ≤ min 1 ((Q:ℝ)/(2*L*(folded k:ℝ))) := by
  have p : (0:ℝ)<Q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne Q))
  have l : (0:ℝ)<L := by exact_mod_cast hL
  have m : (0:ℝ)<folded k := by exact_mod_cast folded_pos hk
  have d := norm_pos_iff.mpr (sub_ne_zero.mpr (std_ne_one hk))
  apply (boxCoeff_bound hL (std_norm k) (std_ne_one hk)).trans
  apply min_le_min_left
  apply (div_le_div_iff₀ (mul_pos l d) (by positivity)).mpr
  have h := (div_le_iff₀ p).mp (std_chord k)
  calc
     2*(2*(L:ℝ)*folded k) = (4*(folded k:ℝ))*L := by ring
     _ ≤ (‖ZMod.stdAddChar k - 1‖*Q)*L := mul_le_mul_of_nonneg_right h l.le
     _ = _ := by ring

#print axioms dft_gridSaw_eq
#print axioms dft_gridSaw_zero
#print axioms normalized_dft_bound
#print axioms box_frequency_bound
end FactorialFourier
