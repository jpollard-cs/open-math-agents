import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr

/-! Finite frequency estimates for a one-sided moving average of the centered
fractional part. A cutoff H balances smoothing error against exponential sums.
Only finite sums occur, so the bounds do not depend on the common denominator. -/

noncomputable section
open Finset Real
namespace FactorialFourier

private lemma integral_power_tail (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b)
    (e : ℝ) (he : e ≤ 0) (hne : e ≠ -1) :
    ∑ j ∈ Ioc a b, (j:ℝ)^e ≤ ((b:ℝ)^(e+1) - (a:ℝ)^(e+1))/(e+1) := by
  have ar : (0:ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have br : (a:ℝ) ≤ b := by exact_mod_cast hab
  have ant : AntitoneOn (fun x : ℝ => x^e) (Set.Icc (a:ℝ) b) :=
    fun _ hx _ _ hxy => Real.rpow_le_rpow_of_nonpos (ar.trans_le hx.1) hxy he
  have bound := AntitoneOn.sum_le_integral_Ico (f := fun x : ℝ => x^e) hab ant
  have miss : (0:ℝ) ∉ Set.uIcc (a:ℝ) b := by
    rw [Set.uIcc_of_le br]; intro h; exact ar.not_ge h.1
  rw [integral_rpow (Or.inr ⟨hne,miss⟩)] at bound
  refine le_of_eq_of_le ?_ bound
  symm
  apply sum_bij (fun i _ => i+1)
  · intro i hi; obtain ⟨l,u⟩ := mem_Ico.mp hi; exact mem_Ioc.mpr ⟨by omega, by omega⟩
  · intros; omega
  · intro j hj; obtain ⟨l,u⟩ := mem_Ioc.mp hj
    exact ⟨j-1,mem_Ico.mpr ⟨by omega,by omega⟩,by omega⟩
  · intros; rfl

private lemma power_initial (H : ℕ) (hH : 1 ≤ H) (k : ℝ) (hk : 0 < k) (hk1 : k ≤ 1) :
    ∑ j ∈ Icc 1 H, (j:ℝ)^(k-1) ≤ (H:ℝ)^k/k := by
  have p := integral_power_tail 1 H (by decide) hH (k-1) (by linarith) (by linarith)
  rw [show k-1+1=k by ring] at p
  simp only [Nat.cast_one,Real.one_rpow] at p
  have ss : Icc 1 H = insert 1 (Ioc 1 H) := by ext i; simp; omega
  rw [ss,sum_insert (by simp),Nat.cast_one,Real.one_rpow]
  apply (add_le_add le_rfl p).trans
  apply (le_div_iff₀ hk).mpr
  rw [add_mul,div_mul_cancel₀ _ hk.ne']
  linarith

private lemma power_tail (H K : ℕ) (hH : 1 ≤ H) (hK : H ≤ K) (k : ℝ) (hk : k < 1) :
    ∑ j ∈ Ioc H K, (j:ℝ)^(k-2) ≤ (H:ℝ)^(k-1)/(1-k) := by
  have a := integral_power_tail H K hH hK (k-2) (by linarith) (by linarith)
  rw [show k-2+1=k-1 by ring] at a
  apply a.trans
  have p : 0 < 1-k := by linarith
  have nonneg := Real.rpow_nonneg (Nat.cast_nonneg K) (k-1)
  rw [show k-1= -(1-k) by ring] at nonneg
  rw [show k-1= -(1-k) by ring, div_neg]
  apply (le_div_iff₀ p).mpr
  rw [neg_mul,div_mul_cancel₀ _ p.ne']
  linarith

/-- The weight allotted to a positive frequency j after smoothing at scale 1/H. -/
def frequencyWeight (H j : ℕ) : ℝ := min 1 ((H:ℝ)/j)/(j:ℝ)

/-- Summing a j^k exponential-sum bound costs O_k(H^k) for 0<k<1. -/
theorem frequency_power (H K : ℕ) (hH : 1 ≤ H) (hK : H ≤ K)
    (k : ℝ) (hk : 0 < k) (hk1 : k < 1) :
    ∑ j ∈ Icc 1 K, frequencyWeight H j * (j:ℝ)^k ≤
      (1/k+1/(1-k))*(H:ℝ)^k := by
  have hR : (0:ℝ) < H := by exact_mod_cast (show 0 < H by omega)
  have lo (j : ℕ) (hj : j ∈ Icc 1 H) :
      frequencyWeight H j * (j:ℝ)^k = (j:ℝ)^(k-1) := by
    obtain ⟨jp,jh⟩ := mem_Icc.mp hj
    have p : (0:ℝ) < j := by exact_mod_cast jp
    rw [frequencyWeight,min_eq_left ((one_le_div p).mpr (by exact_mod_cast jh)),Real.rpow_sub_one p.ne']
    ring
  have hi (j : ℕ) (hj : j ∈ Ioc H K) :
      frequencyWeight H j * (j:ℝ)^k = (H:ℝ)*(j:ℝ)^(k-2) := by
    obtain ⟨jh,_⟩ := mem_Ioc.mp hj
    have p : (0:ℝ) < j := hR.trans (by exact_mod_cast jh)
    rw [frequencyWeight,min_eq_right ((div_le_one p).mpr (by exact_mod_cast jh.le)),
       show k-2=(k-1)-1 by ring,Real.rpow_sub_one p.ne',Real.rpow_sub_one p.ne']
    ring
  have sets : Icc 1 K = Icc 1 H ∪ Ioc H K := by ext j; simp; omega
  have dis : Disjoint (Icc 1 H) (Ioc H K) := by rw [disjoint_left]; intro j hj hh
                                                exact (mem_Ioc.mp hh).1.not_ge (mem_Icc.mp hj).2
  rw [sets,sum_union dis,sum_congr rfl lo,sum_congr rfl hi,← mul_sum]
  apply (add_le_add (power_initial H hH k hk hk1.le)
    (mul_le_mul_of_nonneg_left (power_tail H K hH hK k hk1) hR.le)).trans
  rw [Real.rpow_sub_one hR.ne']
  field_simp; ring_nf; exact le_rfl

/-- A j^{-1} error in the exponential sum costs at most twice its coefficient. -/
theorem frequency_reciprocal (H K : ℕ) :
    ∑ j ∈ Icc 1 K, frequencyWeight H j / j ≤ 2 := by
  by_cases hK : 1 ≤ K
  · have p := power_tail 1 K (by decide) hK 0 (by norm_num)
    norm_num at p
    have ss : Icc 1 K = insert 1 (Ioc 1 K) := by ext i; simp; omega
    calc
      _ ≤ ∑ j ∈ Icc 1 K, (j:ℝ)^(-(2:ℝ)) := by
        apply sum_le_sum; intro j hj
        have jp : (0:ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
        rw [frequencyWeight,Real.rpow_neg jp.le,Real.rpow_two]
        calc _ ≤ (1/(j:ℝ))/j := by gcongr; exact min_le_left _ _
             _ = _ := by field_simp
      _ = 1 + ∑ j ∈ Ioc 1 K, (j:ℝ)^(-(2:ℝ)) := by rw [ss,sum_insert (by simp)]; simp
      _ ≤ 2 := by
        norm_num [Real.rpow_neg,Real.rpow_two] <;> linarith
  · simp [show K=0 by omega]

/-- A smoothed finite Fourier sum can be estimated uniformly in its upper
frequency K using only exponential-sum bounds of the form E*j^k + F/j. -/
theorem frequency_budget (H K : ℕ) (hH : 1 ≤ H) (hK : H ≤ K) (E F k : ℝ)
    (hE : 0 ≤ E) (hF : 0 ≤ F) (hk : 0 < k) (hk1 : k < 1) :
    ∑ j ∈ Icc 1 K, frequencyWeight H j * (E*(j:ℝ)^k + F/j) ≤
      E*((1/k+1/(1-k))*(H:ℝ)^k) + 2*F := by
  calc
    _ = E*(∑ j ∈ Icc 1 K, frequencyWeight H j*(j:ℝ)^k) +
          F*(∑ j ∈ Icc 1 K, frequencyWeight H j / j) := by
      rw [mul_sum,mul_sum,← sum_add_distrib]
      apply sum_congr rfl; intros; ring
    _ ≤ _ := by
      rw [mul_comm 2 F]
      exact add_le_add (mul_le_mul_of_nonneg_left (frequency_power H K hH hK k hk hk1) hE)
        (mul_le_mul_of_nonneg_left (frequency_reciprocal H K) hF)

end FactorialFourier
#print axioms FactorialFourier.frequency_budget
