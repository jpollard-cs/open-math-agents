import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic

/-! Diminishing marginal growth of the divisor function under multiplication.
Written by Codex (AI) at the request of Jordan Pollard. -/
open Finset
open scoped ArithmeticFunction.sigma

namespace FactorialThinning

private theorem common_support {m : ℕ} (hm : m ≠ 0) {S : Finset ℕ} (hs : m.primeFactors ⊆ S) :
    σ 0 m = ∏ p ∈ S, (m.factorization p + 1) := by
  rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hm]
  apply Finset.prod_subset hs
  intro p _ hp
  have hz : m.factorization p = 0 := Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
  simp [hz]

/-- For a ∣ b and c positive, τ(bc)/τ(b) ≤ τ(ac)/τ(a). -/
theorem diminishing (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hab : a ∣ b) :
    σ 0 (b*c) * σ 0 a ≤ σ 0 (a*c) * σ 0 b := by
  let S := (b*c).primeFactors
  have hbc := Nat.mul_ne_zero hb hc
  have hbc' : b ∣ b*c := dvd_mul_right _ _
  have haS := Nat.primeFactors_mono (hab.trans hbc') hbc
  have hbS := Nat.primeFactors_mono hbc' hbc
  have hacS := Nat.primeFactors_mono (Nat.mul_dvd_mul_right hab c) hbc
  rw [common_support hbc (S:=S) (by intro p hp; exact hp),common_support ha haS,
      common_support (Nat.mul_ne_zero ha hc) hacS,common_support hb hbS,
      ←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  apply Finset.prod_le_prod'
  intro p _
  rw [Nat.factorization_mul hb hc, Nat.factorization_mul ha hc]
  simp only [Finsupp.add_apply]
  have h := ((Nat.factorization_le_iff_dvd ha hb).mpr hab) p
  nlinarith only [Nat.mul_le_mul_right (c.factorization p) h]

end FactorialThinning
#print axioms FactorialThinning.diminishing
