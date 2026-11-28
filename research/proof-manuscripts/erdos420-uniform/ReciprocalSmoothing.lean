import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! One-sided moving averages of a sawtooth on a finite cyclic grid.
The pointwise inequalities include discontinuities. Finite Fourier inversion
then factors the transform into the exponential sum over the input phases
and a geometric sum over the shifts. -/

noncomputable section
open Finset
namespace ReciprocalSmoothing

variable {Q : ℕ} [NeZero Q]

/-- Centered fractional part of a point on the grid of denominator Q. -/
def saw (a : ZMod Q) : ℝ := (a.val : ℝ) / Q - 1/2

omit [NeZero Q] in
private lemma saw_add_upper (a : ZMod Q) (j : ℕ) :
    saw (a + (j : ZMod Q)) ≤ saw a + (j:ℝ)/Q := by
  have nle : (a + (j : ZMod Q)).val ≤ a.val + j := by
    apply (ZMod.val_add_le _ _).trans
    rw [ZMod.val_natCast]
    exact Nat.add_le_add_left (Nat.mod_le ..) _
  have rle : ((a + (j : ZMod Q)).val : ℝ) ≤ (a.val:ℝ) + j := by exact_mod_cast nle
  have h := div_le_div_of_nonneg_right rle (Nat.cast_nonneg Q)
  unfold saw
  rw [add_div] at h
  linarith

omit [NeZero Q] in
private lemma saw_sub_lower (a : ZMod Q) (j : ℕ) :
    saw a ≤ saw (a - (j : ZMod Q)) + (j:ℝ)/Q := by
  simpa only [sub_add_cancel] using saw_add_upper (a - (j : ZMod Q)) j

private lemma sum_shift {L : ℕ} (hL : 0 < L) :
    (∑ j ∈ range L, (j:ℝ)/(Q:ℝ)) = (L:ℝ)*((L:ℝ)-1)/(2*Q) := by
  have hq : (Q:ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have eqn := Finset.sum_range_id_mul_two L
  have eqr : (∑ j ∈ range L, (j:ℝ)) * 2 = (L:ℝ)*((L:ℝ)-1) := by
    have e := congrArg (fun a : ℕ => (a:ℝ)) eqn
    push_cast [Nat.cast_sub (by omega : 1 ≤ L)] at e
    exact e
  rw [← sum_div]
  field_simp
  linear_combination eqr

/-- Upper and lower one-sided moving averages, with their exact mean shift. -/
theorem squeeze (a : ZMod Q) {L : ℕ} (hL : 0 < L) :
    ((∑ j ∈ range L, saw (a + (j : ZMod Q)))/(L:ℝ) - ((L:ℝ)-1)/(2*Q) ≤ saw a) ∧
    (saw a ≤ (∑ j ∈ range L, saw (a - (j : ZMod Q)))/(L:ℝ) + ((L:ℝ)-1)/(2*Q)) := by
  have lp : (0:ℝ) < L := by exact_mod_cast hL
  have h₁ := Finset.sum_le_sum (s := range L) (fun j _ => saw_add_upper a j)
  have h₂ := Finset.sum_le_sum (s := range L) (fun j _ => saw_sub_lower a j)
  simp only [sum_add_distrib, sum_const, card_range, nsmul_eq_mul, sum_shift (Q:=Q) hL] at h₁ h₂
  constructor
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ lp).mpr
    linarith only [h₁, show ((L:ℝ)-1)/(2*Q)*L = L*((L:ℝ)-1)/(2*Q) by ring,
      show (saw a + ((L:ℝ)-1)/(2*Q))*L = (L:ℝ)*saw a + ((L:ℝ)-1)/(2*Q)*L by ring]
  · apply sub_le_iff_le_add.mp
    apply (le_div_iff₀ lp).mpr
    linarith only [h₂, show (saw a - ((L:ℝ)-1)/(2*Q))*L = (L:ℝ)*saw a - L*((L:ℝ)-1)/(2*Q) by ring]

/-- Fourier expansion of a translated sum over two independent lists. -/
theorem fourier_factor {ι κ : Type*} (s : Finset ι) (b : Finset κ) (p : ι → ZMod Q)
    (t : κ → ZMod Q) (f : ZMod Q → ℂ) :
    (∑ i ∈ s, ∑ j ∈ b, f (p i + t j)) =
    (Q:ℂ)⁻¹ * ∑ k : ZMod Q, ZMod.dft f k *
      (∑ i ∈ s, ZMod.stdAddChar (k*p i)) * (∑ j ∈ b, ZMod.stdAddChar (k*t j)) := by
  have invert (a : ZMod Q) : f a =
      (Q:ℂ)⁻¹ * ∑ k : ZMod Q, ZMod.stdAddChar (k*a) * ZMod.dft f k := by
    simpa only [smul_eq_mul, LinearEquiv.symm_apply_apply] using
      (ZMod.invDFT_apply (ZMod.dft f) a)
  calc
    _ = ∑ i ∈ s, ∑ j ∈ b, ((Q:ℂ)⁻¹ *
          ∑ k : ZMod Q, ZMod.dft f k * ZMod.stdAddChar (k*p i) * ZMod.stdAddChar (k*t j)) := by
        apply sum_congr rfl; intro i _
        apply sum_congr rfl; intro j _
        rw [invert, mul_right_inj' (inv_ne_zero (by exact_mod_cast (NeZero.ne Q)))]
        apply sum_congr rfl; intro k _
        rw [mul_add,AddChar.map_add_eq_mul]
        ring
    _ = (Q:ℂ)⁻¹ * ∑ i ∈ s, ∑ k : ZMod Q, ∑ j ∈ b,
          ZMod.dft f k * ZMod.stdAddChar (k*p i) * ZMod.stdAddChar (k*t j) := by
      simp only [mul_sum]
      apply sum_congr rfl; intro i _
      rw [sum_comm]
    _ = _ := by
      congr 1
      rw [sum_comm]
      apply sum_congr rfl; intro k _
      symm
      calc
        _ = (∑ i ∈ s, ZMod.dft f k * ZMod.stdAddChar (k*p i)) *
            (∑ j ∈ b, ZMod.stdAddChar (k*t j)) := by rw [← mul_sum]
        _ = ∑ i ∈ s, (ZMod.dft f k * ZMod.stdAddChar (k*p i)) *
            (∑ j ∈ b, ZMod.stdAddChar (k*t j)) := by rw [sum_mul]
        _ = _ := by simp only [mul_sum]

/-- Smoothing with the reflected shifts has the same spectral magnitudes. -/
private lemma reflected_box (k : ZMod Q) (L : ℕ) :
    ‖∑ j ∈ range L, ZMod.stdAddChar (k * -(j : ZMod Q))‖ =
    ‖∑ j ∈ range L, ZMod.stdAddChar (k * (j : ZMod Q))‖ := by
  have h (j : ℕ) : ZMod.stdAddChar (k * -(j : ZMod Q)) =
      (starRingEnd ℂ) (ZMod.stdAddChar (k * (j : ZMod Q))) := by
    rw [mul_neg,ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
    rfl
  simp only [h, ← map_sum, Complex.norm_conj]

/-- The error from smoothing a sample of residues is bounded by a Fourier
sum. The mean shift accounts for possible jumps at the grid origin. -/
theorem discrepancy_bound {ι : Type*} (s : Finset ι) (p : ι → ZMod Q)
    {L : ℕ} (hL : 0 < L) :
    |∑ i ∈ s, saw (p i)| ≤
      (s.card:ℝ)*((L:ℝ)-1)/(2*Q) +
      (∑ k : ZMod Q, ‖ZMod.dft (fun a => (saw a : ℂ)) k‖ *
        ‖∑ i ∈ s, ZMod.stdAddChar (k*p i)‖ *
        ‖∑ j ∈ range L, ZMod.stdAddChar (k*(j : ZMod Q))‖)/((Q:ℝ)*L) := by
  let f : ZMod Q → ℂ := fun a => (saw a : ℂ)
  let spec := ∑ k : ZMod Q, ‖ZMod.dft f k‖ *
    ‖∑ i ∈ s, ZMod.stdAddChar (k*p i)‖ *
    ‖∑ j ∈ range L, ZMod.stdAddChar (k*(j : ZMod Q))‖
  have qp : (0:ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have lp : (0:ℝ) < L := by exact_mod_cast hL
  have shift_bound (t : ℕ → ZMod Q)
      (ht : ∀ k : ZMod Q, ‖∑ j ∈ range L, ZMod.stdAddChar (k*t j)‖ =
        ‖∑ j ∈ range L, ZMod.stdAddChar (k*(j : ZMod Q))‖) :
      |∑ i ∈ s, ∑ j ∈ range L, saw (p i+t j)|/(L:ℝ) ≤ spec/((Q:ℝ)*L) := by
    have hf := fourier_factor s (range L) p t f
    have bound := norm_sum_le (univ : Finset (ZMod Q)) (fun k =>
      ZMod.dft f k * (∑ i ∈ s, ZMod.stdAddChar (k*p i)) *
        (∑ j ∈ range L, ZMod.stdAddChar (k*t j)))
    simp only [norm_mul, ht] at bound
    have normleft : ‖∑ i ∈ s, ∑ j ∈ range L, f (p i + t j)‖ =
        |∑ i ∈ s, ∑ j ∈ range L, saw (p i + t j)| := by
      simp only [f, ← Complex.ofReal_sum, Complex.norm_real, Real.norm_eq_abs]
    have absbound : |∑ i ∈ s, ∑ j ∈ range L, saw (p i+t j)| ≤ (Q:ℝ)⁻¹*spec := by
      rw [← normleft,hf,norm_mul,norm_inv,Complex.norm_natCast]
      exact mul_le_mul_of_nonneg_left bound (by positivity)
    apply (div_le_div_of_nonneg_right absbound lp.le).trans_eq
    field_simp
  have upper := shift_bound (fun j => -(j:ZMod Q)) (fun k => reflected_box k L)
  have lower := shift_bound (fun j => (j:ZMod Q)) (fun _ => rfl)
  simp only [← sub_eq_add_neg] at upper
  have h₁ := Finset.sum_le_sum (s := s) (fun i _ => (squeeze (p i) hL).1)
  have h₂ := Finset.sum_le_sum (s := s) (fun i _ => (squeeze (p i) hL).2)
  simp only [sum_sub_distrib,sum_add_distrib,← sum_div,sum_const,nsmul_eq_mul] at h₁ h₂
  have up := (div_le_div_of_nonneg_right (le_abs_self _) lp.le).trans upper
  have lo := (div_le_div_of_nonneg_right (neg_le_abs _) lp.le).trans lower
  change _ ≤ _ + spec/((Q:ℝ)*L)
  rw [abs_le]
  rw [neg_div] at lo
  rw [← mul_sub] at h₁ h₂
  constructor <;> linarith only [h₁,h₂,up,lo]

/-- Normalized form. The box multiplier is the mean of successive powers
of a root of unity, so coefficient bounds apply to each frequency. -/
theorem normalized_discrepancy {ι : Type*} (s : Finset ι) (p : ι → ZMod Q)
    {L : ℕ} (hL : 0 < L) :
    |∑ i ∈ s, saw (p i)| ≤ (s.card:ℝ)*((L:ℝ)-1)/(2*Q) +
      ∑ k : ZMod Q, (‖ZMod.dft (fun a => (saw a : ℂ)) k‖/(Q:ℝ)) *
        ‖∑ i ∈ s, ZMod.stdAddChar (k*p i)‖ *
        ‖(∑ j ∈ range L, (ZMod.stdAddChar k)^j)/(L:ℂ)‖ := by
  apply (discrepancy_bound s p hL).trans_eq
  congr 1
  rw [sum_div]
  apply sum_congr rfl; intro k _
  have h (j : ℕ) : ZMod.stdAddChar (k*(j:ZMod Q)) = (ZMod.stdAddChar k)^j := by
    rw [mul_comm,← nsmul_eq_mul,AddChar.map_nsmul_eq_pow]
  simp only [h,norm_div,Complex.norm_natCast]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end ReciprocalSmoothing

#print axioms ReciprocalSmoothing.squeeze
#print axioms ReciprocalSmoothing.fourier_factor
#print axioms ReciprocalSmoothing.discrepancy_bound
#print axioms ReciprocalSmoothing.normalized_discrepancy
