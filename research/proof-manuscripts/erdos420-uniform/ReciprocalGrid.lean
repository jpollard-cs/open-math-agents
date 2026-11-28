import FactorialSelbergBlock

/-! Exact realization of the reciprocal phases and their centered fractional
parts on a common finite grid. Its denominator may be enlarged arbitrarily. -/
noncomputable section
open Finset
namespace FactorialFourier

/-- Residue of x/m on the Q-grid when m divides Q. -/
def residue (Q x m : ℕ) : ZMod Q := ((x*(Q/m) : ℕ) : ZMod Q)

lemma residue_val {Q m : ℕ} [NeZero Q] (hm : 0 < m) (hd : m ∣ Q) (x : ℕ) :
    (residue Q x m).val = x % m * (Q/m) := by
  have h := Nat.div_mul_cancel hd
  rw [residue,ZMod.val_natCast]
  conv_lhs => arg 2; rw [← h,mul_comm]
  exact Nat.mul_mod_mul_right (Q/m) x m

theorem residue_saw {Q m : ℕ} [NeZero Q] (hm : 0 < m) (hd : m ∣ Q) (x : ℕ) :
    ((residue Q x m).val : ℝ)/Q-1/2 = FactorialSieve.saw x m := by
  rw [residue_val hm hd,FactorialSieve.saw,Nat.cast_mul]
  have h : ((Q/m:ℕ):ℝ)*m=(Q:ℝ) := by exact_mod_cast Nat.div_mul_cancel hd
  have qp : (0:ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have mp : (0:ℝ) < m := by exact_mod_cast hm
  have t : ((x%m:ℕ):ℝ)*(Q/m:ℕ)/Q=((x%m:ℕ):ℝ)/m := by
    apply (div_eq_div_iff qp.ne' mp.ne').mpr
    rw [mul_assoc,h]
  exact sub_left_inj.mpr t

/-- The Fourier coefficients of the list of residues are genuine
exponential sums in the reciprocal phase x/m. -/
theorem residue_character {Q m : ℕ} [NeZero Q] (hm : 0 < m) (hd : m ∣ Q) (x j : ℕ) :
    ZMod.stdAddChar ((j : ZMod Q)*residue Q x m) =
      Complex.exp (2*Real.pi*Complex.I*(j:ℂ)*x/m) := by
  rw [residue,← Nat.cast_mul,ZMod.stdAddChar_apply,ZMod.toCircle_natCast]
  push_cast
  congr 1
  have h : ((Q/m:ℕ):ℂ)*m=(Q:ℂ) := by exact_mod_cast Nat.div_mul_cancel hd
  have qp : (Q:ℂ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  have mp : (m:ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  apply (div_eq_div_iff qp mp).mpr
  linear_combination (2*(Real.pi:ℂ)*Complex.I*j*x)*h

/-- A common denominator whose size can be chosen independently of the
frequency cutoff, including when the interval is empty. -/
theorem exists_grid (v : ℝ) (H : ℕ)  :
    ∃ L : ℕ, 2 ≤ L ∧ ∀ m : ℕ, 0 < m → m ≤ ⌊v⌋₊ → m ∣ H*L := by
  refine ⟨2*Nat.factorial ⌊v⌋₊,by nlinarith [Nat.factorial_pos ⌊v⌋₊],?_⟩
  intro m hm hv
  exact dvd_mul_of_dvd_right (dvd_mul_of_dvd_right (Nat.dvd_factorial hm hv) 2) H

theorem remainder_grid {Q : ℕ} [NeZero Q] (u v : ℝ) (x t : ℕ)
    (hQ : ∀ m : ℕ, 0 < m → m ≤ ⌊v⌋₊ → m ∣ Q) :
    FactorialSieve.remainder u v x t =
      ∑ m ∈ (Ioc ⌊u⌋₊ ⌊v⌋₊).filter (t ∣ ·), (((residue Q x m).val : ℝ)/Q-1/2) := by
  rw [FactorialSieve.remainder,sum_filter]
  apply sum_congr rfl; intro m hm
  split_ifs
  · obtain ⟨lo,hi⟩ := mem_Ioc.mp hm
    have mp : 0 < m := by omega
    exact (residue_saw mp (hQ m mp hi) x).symm
  · rfl

end FactorialFourier
#print axioms FactorialFourier.residue_character
#print axioms FactorialFourier.remainder_grid
