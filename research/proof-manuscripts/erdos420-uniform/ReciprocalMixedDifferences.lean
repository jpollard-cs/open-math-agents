import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Mixed finite differences of reciprocal powers. A shift acts by
$D_h f(x)=f(x)-f(x+h)$. The two bounds retain the product of all shifts.
They apply before and after every differencing step in the factorial sieve. -/
noncomputable section
open Set

namespace FactorialReciprocal

/-- Iteratively difference the reciprocal power, with the completely monotone sign. -/
def diffPow : List ℝ → ℕ → ℝ → ℝ
  | [], p, x => (x^p)⁻¹
  | h :: hs, p, x => diffPow hs p x - diffPow hs p (x+h)

/-- Differentiating a mixed difference raises the reciprocal power by one. -/
theorem hasDerivAt_diffPow (hs : List ℝ) (p : ℕ) {x : ℝ} (hx : 0 < x)
    (nonneg : ∀ h ∈ hs, 0 ≤ h) :
    HasDerivAt (diffPow hs p) (-(p:ℝ)*diffPow hs (p+1) x) x := by
  induction hs generalizing x with
  | nil =>
    cases p with
    | zero => simpa [diffPow] using (hasDerivAt_const x (1:ℝ))
    | succ p =>
      have hd := (hasDerivAt_pow (p+1) x).inv (pow_ne_zero _ hx.ne')
      apply hd.congr_deriv
      change -(↑(p+1) * x^(p+1-1)) / (x^(p+1))^2 = -(↑(p+1):ℝ) * (x^(p+1+1))⁻¹
      rw [Nat.add_sub_cancel, pow_succ x (p+1), pow_succ x p]
      field_simp
  | cons h hs ih =>
    have h0 := nonneg h (by simp)
    have ht : ∀ y ∈ hs, 0 ≤ y := fun y hy => nonneg y (by simp [hy])
    have A := ih hx ht
    have B := (ih (x := x+h) (by linarith) ht).comp_add_const x h
    apply (A.sub B).congr_deriv
    change -(p:ℝ)*diffPow hs (p+1) x - (-(p:ℝ)*diffPow hs (p+1) (x+h)) =
      -(p:ℝ)*(diffPow hs (p+1) x - diffPow hs (p+1) (x+h))
    ring

private lemma jump (hs : List ℝ) (p : ℕ) {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    (nonneg : ∀ a ∈ hs, 0 ≤ a) :
    ∃ y ∈ Ioo x (x+h), diffPow (h::hs) p x = (h*p)*diffPow hs (p+1) y := by
  have hder (y : ℝ) (hy : 0 < y) := hasDerivAt_diffPow hs p hy nonneg
  obtain ⟨y,hy,eq⟩ := exists_hasDerivAt_eq_slope (diffPow hs p)
    (fun y => -(p:ℝ)*diffPow hs (p+1) y) (show x<x+h by linarith)
    (fun y hy => (hder y (lt_of_lt_of_le hx hy.1)).continuousAt.continuousWithinAt)
    (fun y hy => hder y (hx.trans hy.1))
  use y, hy
  rw [show x+h-x=h by ring] at eq
  have eq' := (eq_div_iff hh.ne').mp eq
  dsimp [diffPow]
  linarith only [show (-(p:ℝ)*diffPow hs (p+1) y)*h= -(h*p*diffPow hs (p+1) y) by ring,eq']

/-- Uniform estimates for arbitrarily many shifts on an interval away from zero. -/
theorem diffPow_bounds (hs : List ℝ) (p : ℕ) {x : ℝ} (hx : 0 < x)
    (nonneg : ∀ h ∈ hs, 0 ≤ h) :
    (p.ascFactorial hs.length : ℝ) * hs.prod / (x+hs.sum)^(p+hs.length) ≤ diffPow hs p x ∧
    diffPow hs p x ≤ (p.ascFactorial hs.length : ℝ) * hs.prod / x^(p+hs.length) := by
  induction hs generalizing p x with
  | nil => simp [diffPow,one_div]
  | cons h hs ih =>
    have h0 := nonneg h (by simp)
    have ht : ∀ a ∈ hs, 0 ≤ a := fun a ha => nonneg a (by simp [ha])
    by_cases zero : h=0
    · simp [zero,diffPow]
    have hh := lt_of_le_of_ne h0 (Ne.symm zero)
    obtain ⟨y,hy,eq⟩ := jump hs p hx hh ht
    have yp := hx.trans hy.1
    obtain ⟨lo,hi⟩ := ih (p+1) yp ht
    let b : ℝ := ((p+1).ascFactorial hs.length : ℝ) * hs.prod
    have posprod := List.prod_nonneg ht
    have bnon : 0 ≤ b := by dsimp [b]; positivity
    have ssum := List.sum_nonneg ht
    have coeff : (p.ascFactorial (h::hs).length : ℝ) * (h::hs).prod = (h*p)*b := by
      have fac : p.ascFactorial (hs.length+1) = p*(p+1).ascFactorial hs.length :=
        Nat.ascFactorial_succ.trans (Nat.succ_ascFactorial p hs.length).symm
      simp only [List.length_cons, List.prod_cons,fac,Nat.cast_mul]
      dsimp [b]
      ring
    have expo : p+(h::hs).length = (p+1)+hs.length := by simp; omega
    rw [coeff,expo, List.sum_cons, eq]
    change b/(y+hs.sum)^_ ≤ _ at lo
    change _ ≤ b/y^_ at hi
    have hp : 0 ≤ h*(p:ℝ) := by positivity
    constructor
    · rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hp
      apply le_trans _ lo
      apply div_le_div_of_nonneg_left bnon (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by linarith [hy.2]) _
    · rw [mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ hp
      apply hi.trans
      apply div_le_div_of_nonneg_left bnon (by positivity)
      exact pow_le_pow_left₀ hx.le hy.1.le _

/-- With nonnegative shifts every mixed reciprocal difference is nonnegative. -/
theorem diffPow_nonneg (hs : List ℝ) (p : ℕ) {x : ℝ} (hx : 0 < x)
    (nonneg : ∀ h ∈ hs, 0 ≤ h) : 0 ≤ diffPow hs p x := by
  have hp := List.prod_nonneg nonneg
  have hsum := List.sum_nonneg nonneg
  exact le_trans (by positivity) (diffPow_bounds hs p hx nonneg).1

/-- All these signed differences decrease with their base point. -/
theorem diffPow_antitoneOn (hs : List ℝ) (p : ℕ) (nonneg : ∀ h ∈ hs, 0 ≤ h) :
    AntitoneOn (diffPow hs p) (Ioi 0) := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl|lt
  · exact le_rfl
  obtain ⟨w, hw, step⟩ := jump hs p hx (sub_pos.mpr lt) nonneg
  have h := diffPow_nonneg hs (p+1) (lt_trans hx hw.1) nonneg
  have good : 0 ≤ ((y-x)*p)*diffPow hs (p+1) w :=
    mul_nonneg (mul_nonneg (sub_nonneg.mpr lt.le) (Nat.cast_nonneg _)) h
  have val := good.trans step.ge
  change 0 ≤ diffPow hs p x - diffPow hs p (x+(y-x)) at val
  rw [show x+(y-x)=y by ring] at val
  exact sub_nonneg.mp val

/-- Exact derivatives of every order, including the shifted phases of the A process. -/
theorem iteratedDeriv_diffPow (hs : List ℝ) (p r : ℕ) {x : ℝ} (hx : 0 < x)
    (nonneg : ∀ h ∈ hs, 0 ≤ h) :
    iteratedDeriv r (diffPow hs p) x = (-1:ℝ)^r*(p.ascFactorial r : ℝ)*diffPow hs (p+r) x := by
  induction r generalizing p with
  | zero => simp
  | succ r ih =>
    have agree : Set.EqOn (deriv (diffPow hs p)) (fun y => -(p:ℝ)*diffPow hs (p+1) y) (Ioi 0) :=
      fun y hy => (hasDerivAt_diffPow hs p hy nonneg).deriv
    have eq := agree.iteratedDeriv_of_isOpen isOpen_Ioi r (show x∈Ioi 0 from hx)
    rw [iteratedDeriv_succ',eq,iteratedDeriv_const_mul_field, ih]
    have fac : p.ascFactorial (r+1)=p*(p+1).ascFactorial r :=
      Nat.ascFactorial_succ.trans (Nat.succ_ascFactorial p r).symm
    rw [fac, Nat.cast_mul, pow_succ,show p+1+r=p+(r+1) by omega]
    ring

/-- The r-th derivative of the mixed reciprocal phase has one sign. Its absolute
size lies between the corresponding derivatives at the two extreme endpoints. -/
theorem shifted_reciprocal_derivative_bounds (hs : List ℝ) (r : ℕ)
    {x : ℝ} (hx : 0 < x) (nonneg : ∀ h ∈ hs, 0 ≤ h) :
    ((r+hs.length).factorial : ℝ)*hs.prod/(x+hs.sum)^(r+hs.length+1) ≤
      |iteratedDeriv r (diffPow hs 1) x| ∧
    |iteratedDeriv r (diffPow hs 1) x| ≤
      ((r+hs.length).factorial : ℝ)*hs.prod/x^(r+hs.length+1) := by
  rw [iteratedDeriv_diffPow hs 1 r hx nonneg]
  simp only [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,Nat.one_ascFactorial,
    abs_of_nonneg (Nat.cast_nonneg r.factorial : (0:ℝ) ≤ (r.factorial:ℝ)), abs_of_nonneg (diffPow_nonneg hs (1+r) hx nonneg)]
  obtain ⟨lo,hi⟩ := diffPow_bounds hs (1+r) hx nonneg
  have fac : (r.factorial : ℝ) * ((1+r).ascFactorial hs.length : ℝ) =
      ((r+hs.length).factorial : ℝ) := by
    exact_mod_cast (by simpa [Nat.add_comm 1 r] using Nat.factorial_mul_ascFactorial r hs.length :
      r.factorial * (1+r).ascFactorial hs.length = (r+hs.length).factorial)
  have expEq : 1+r+hs.length = r+hs.length+1 := by omega
  rw [expEq] at lo hi
  have left := mul_le_mul_of_nonneg_left lo (Nat.cast_nonneg r.factorial : (0:ℝ) ≤ _)
  have right := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg r.factorial : (0:ℝ) ≤ _)
  rw [← mul_div_assoc, ← mul_assoc, fac] at left right
  exact ⟨left,right⟩

end FactorialReciprocal
#print axioms FactorialReciprocal.diffPow_bounds
#print axioms FactorialReciprocal.diffPow_antitoneOn
#print axioms FactorialReciprocal.iteratedDeriv_diffPow
#print axioms FactorialReciprocal.shifted_reciprocal_derivative_bounds
