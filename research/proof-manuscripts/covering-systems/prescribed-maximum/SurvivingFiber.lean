import Mathlib

namespace PrescribedMaximum

/-- If at most three classes per nonzero 5-level remove points from
    5^a = 4 * S + 1 rows, more than S rows survive. -/
theorem surviving_rows (K S : ℕ) (h : 4 * S + 1 ≤ K + 3 * S) : S < K := by
  omega

/-- The geometric budget for the remaining classes, for arbitrary depth b. -/
theorem block_budget (K S q : ℕ) (hs : S < K) (hq : 7 ≤ q) (b : ℕ) :
    ∑ j ∈ Finset.range b, 3 * (K + S) * q ^ j < K * q ^ b := by
  induction b with
  | zero => simp; omega
  | succ b ih =>
    have h1 : K + 3 * (K + S) ≤ 7 * K := by omega
    have h2 := Nat.mul_le_mul_right (q ^ b)
      (h1.trans (Nat.mul_le_mul_right K hq))
    rw [Finset.sum_range_succ, pow_succ]
    calc
      _ < K * q ^ b + 3 * (K + S) * q ^ b := Nat.add_lt_add_right ih _
      _ = (K + 3 * (K + S)) * q ^ b := by ring
      _ ≤ (q * K) * q ^ b := h2
      _ = _ := by ring

/-- A finite union satisfying the digit-level incidence budgets misses a point
    of any surviving CRT grid of the given size. -/
theorem exists_uncovered {Point : Type*} [DecidableEq Point]
    (grid : Finset Point) (level : ℕ → Finset Point) (K S q b : ℕ)
    (hs : S < K) (hq : 7 ≤ q) (hgrid : grid.card = K * q ^ b)
    (hc : ∀ j ∈ Finset.range b, (level j).card ≤ 3 * (K + S) * q ^ j) :
    ∃ x ∈ grid, x ∉ (Finset.range b).biUnion level := by
  by_contra! h
  have hsub : grid ⊆ (Finset.range b).biUnion level := h
  have hle := (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le.trans (Finset.sum_le_sum hc))
  rw [hgrid] at hle
  exact (Nat.not_le_of_lt (block_budget K S q hs hq b)) hle

theorem fraction_at_175 : (3 : ℚ) * (1 + 5 / 7 + 1 / 7) / 6 = 13 / 14 := by
  norm_num

#print axioms exists_uncovered
#print axioms fraction_at_175
end PrescribedMaximum
