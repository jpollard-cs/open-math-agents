import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Bounds for a symmetric spectrum on a finite cyclic group. -/
noncomputable section
open Finset
namespace FactorialFourier
variable {Q : ℕ} [NeZero Q]

/-- Each positive distance from zero is represented by at most two frequencies. -/
theorem sum_folded (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j) :
    (∑ k ∈ (univ : Finset (ZMod Q)).erase 0, f (min k.val (Q-k.val)))
      ≤ 2*∑ j ∈ Icc 1 Q, f j := by
  classical
  let S := (univ : Finset (ZMod Q)).erase 0
  let P (k : ZMod Q) := k.val ≤ Q-k.val
  have positive {k : ZMod Q} (hk : k ∈ S) : 0 < k.val := by
    by_contra! h
    have hz : k.val=0 := by omega
    exact (mem_erase.mp hk).1 (by simpa using congrArg (fun n : ℕ => (n:ZMod Q)) hz)
  have left : ∑ k ∈ S.filter P, f (min k.val (Q-k.val)) ≤ ∑ j ∈ Icc 1 Q, f j := by
    let A := S.filter P
    have maps : A.image ZMod.val ⊆ Icc 1 Q := by
      intro j hj; obtain ⟨k,hk,rfl⟩ := mem_image.mp hj
      exact mem_Icc.mpr ⟨positive (mem_filter.mp hk).1,k.val_lt.le⟩
    calc
      _ = ∑ k ∈ A, f k.val := sum_congr rfl (fun k hk => by rw [min_eq_left (mem_filter.mp hk).2])
      _ = ∑ j ∈ A.image ZMod.val, f j := (sum_image (f:=f) (ZMod.val_injective Q).injOn).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg maps (fun j _ _ => hf j)
  have right : ∑ k ∈ S.filter (fun k => ¬ P k), f (min k.val (Q-k.val)) ≤ ∑ j ∈ Icc 1 Q, f j := by
    let A := S.filter (fun k => ¬ P k)
    let g (k : ZMod Q) := Q-k.val
    have maps : A.image g ⊆ Icc 1 Q := by
      intro j hj; obtain ⟨k,_,rfl⟩ := mem_image.mp hj
      have hh := k.val_lt; dsimp [g]; exact mem_Icc.mpr ⟨by omega,by omega⟩
    have inj : Set.InjOn g A := by
      intro a _ b _ eq
      have ha := a.val_lt; have hb := b.val_lt
      apply ZMod.val_injective Q; dsimp [g] at eq; omega
    calc
      _ = ∑ k ∈ A, f (g k) := sum_congr rfl (fun k hk => by
        exact congrArg f (min_eq_right (le_of_not_ge ((mem_filter.mp hk).2 : ¬ P k))))
      _ = ∑ j ∈ A.image g, f j := (sum_image (f:=f) inj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg maps (fun j _ _ => hf j)
  change (∑ k ∈ S, _) ≤ _
  rw [← sum_filter_add_sum_filter_not S P,two_mul]
  exact add_le_add left right

/-- Reflection in the cyclic group conjugates the exponential sum. -/
theorem norm_spectrum_neg {ι : Type*} (s : Finset ι) (p : ι → ZMod Q) (k : ZMod Q) :
    ‖∑ i ∈ s, ZMod.stdAddChar ((-k)*p i)‖ = ‖∑ i ∈ s, ZMod.stdAddChar (k*p i)‖ := by
  have h (a : ZMod Q) : ZMod.stdAddChar (-a) = star (ZMod.stdAddChar a) := by
    rw [ZMod.stdAddChar_apply,AddChar.map_neg_eq_inv,Circle.coe_inv_eq_conj]
    rfl
  simp only [neg_mul,h,← star_sum]
  exact norm_star _

/-- A bound for positive integer frequencies automatically applies to their
folded representatives, including the order-two character when Q is even. -/
theorem spectrum_folded {ι : Type*} (s : Finset ι) (p : ι → ZMod Q) (f : ℕ → ℝ)
    (B : ∀ j : ℕ, 0 < j → ‖∑ i ∈ s, ZMod.stdAddChar ((j:ZMod Q)*p i)‖ ≤ f j)
    {k : ZMod Q} (hk : k≠0) :
    ‖∑ i ∈ s, ZMod.stdAddChar (k*p i)‖ ≤ f (min k.val (Q-k.val)) := by
  by_cases h : k.val ≤ Q-k.val
  · rw [min_eq_left h]
    have pos : 0 < k.val := by
      by_contra! hh
      apply hk
      have hz : k.val=0 := by omega
      simpa using congrArg (fun n : ℕ => (n:ZMod Q)) hz
    simpa using B k.val pos
  · rw [min_eq_right (le_of_not_ge h)]
    have pos : 0 < Q-k.val := Nat.sub_pos_of_lt k.val_lt
    have c : ((Q-k.val:ℕ):ZMod Q) = -k := by
      rw [Nat.cast_sub k.val_lt.le]; simp
    have b := B _ pos
    rwa [c,norm_spectrum_neg] at b

end FactorialFourier
#print axioms FactorialFourier.sum_folded
#print axioms FactorialFourier.spectrum_folded
