import Mathlib

/-! A finite substitute for the limiting integral in the four-ninths sieve.
The 48 bands have fixed endpoints on the logarithmic scale. -/
noncomputable section
open Finset Real
open scoped Classical

namespace PrimeBlockMesh

/-- Equal subdivisions within each of the three exponent-pair ranges. -/
def edge (j : ℕ) : ℚ :=
  if j ≤ 16 then 4/9 + j*(77/162-4/9)/16
  else if j ≤ 32 then 77/162 + ((j-16 : ℕ) : ℚ)*(29/54-77/162)/16
  else 29/54 + ((j-32 : ℕ) : ℚ)*(50009/90000-29/54)/16

/-- An upper allowance per window position for unweighted prime hits in band j.
The additive tolerance absorbs the eventual error in the local sieve estimate. -/
def allowance (j : ℕ) : ℚ :=
  let v := edge (j+1)
  let θ := if j < 16 then (4/7)/(17/42-(5/7)*v)
           else if j < 32 then 1/(19/54-v/2) else 12
  (v-edge j)*θ + 1/1000000

set_option maxRecDepth 4000 in
theorem budget : (4/9 : ℚ) + ∑ j ∈ range 48, edge (j+1)*allowance j < 2499/2500 := by
  decide +kernel

private lemma crossing (f : ℕ → ℝ) (x : ℝ) (h0 : f 0 < x) (k : ℕ) (hk : x ≤ f k) :
    ∃ j < k, f j < x ∧ x ≤ f (j+1) := by
  induction k with
  | zero => exact (not_lt_of_ge hk h0).elim
  | succ k ih =>
    by_cases hend : x ≤ f k
    · obtain ⟨j, hj, lo, hi⟩ := ih hend
      exact ⟨j, by omega, lo, hi⟩
    · exact ⟨k, by omega, lt_of_not_ge hend, hk⟩

/-- The log weight of any set of hits in the complete middle range is bounded
by the finite unweighted counts. S can label a prime together with its position. -/
theorem first_power_mass {α : Type*} (S : Finset α) (p : α → ℕ) (n h : ℕ) (hn : 1 ≤ n)
    (range_hits : ∀ z ∈ S, (n:ℝ)^(4/9:ℝ) < (p z:ℝ) ∧
      (p z:ℝ) ≤ (n:ℝ)^(5/9+1/10000:ℝ))
    (counts : ∀ j < 48,
      ((S.filter (fun z => (n:ℝ)^(edge j : ℝ) < (p z:ℝ) ∧
        (p z:ℝ) ≤ (n:ℝ)^(edge (j+1) : ℝ))).card : ℝ) ≤ (allowance j : ℝ)*h) :
    (∑ z ∈ S, log (p z)) ≤ (5/9-1/2500)*(h:ℝ)*log n := by
  let bin (j : ℕ) := S.filter (fun z => (n:ℝ)^(edge j : ℝ) < (p z:ℝ) ∧
                                      (p z:ℝ) ≤ (n:ℝ)^(edge (j+1) : ℝ))
  let cap (j : ℕ) := (edge (j+1) : ℝ)*log n
  have hn0 : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have cap_pos (j : ℕ) : 0 ≤ cap j := by
    have edge_nonneg : 0 ≤ edge (j+1) := by
      unfold edge
      split
      · norm_num
        positivity
      · split <;> norm_num <;> positivity
    exact mul_nonneg (by exact_mod_cast edge_nonneg) (Real.log_natCast_nonneg n)
  have cover (z : α) (hz : z ∈ S) :
      ∃ j < 48, z ∈ bin j ∧ log (p z) ≤ cap j := by
    obtain ⟨hlo,hhi⟩ := range_hits z hz
    let f (j : ℕ) := (n:ℝ)^(edge j : ℝ)
    have hzero : f 0 < (p z:ℝ) := by simpa [f,edge] using hlo
    have hlast : (p z:ℝ) ≤ f 48 := by norm_num [f,edge]; convert hhi using 2 <;> norm_num
    obtain ⟨j, hj, lo, hi⟩ := crossing f (p z) hzero 48 hlast
    have pp : (0:ℝ) < p z := (Real.rpow_pos_of_pos hn0 _).trans lo
    refine ⟨j,hj,mem_filter.mpr ⟨hz, lo, hi⟩, ?_⟩
    simpa only [f, cap, log_rpow hn0] using Real.log_le_log pp hi
  have point (z : α) (hz : z ∈ S) : log (p z) ≤ ∑ j ∈ range 48, if z ∈ bin j then cap j else 0 := by
    obtain ⟨j,hj,hmem,hle⟩ := cover z hz
    apply hle.trans
    have hs := Finset.single_le_sum (f := fun j => if z ∈ bin j then cap j else 0)
      (fun j (_ : j ∈ range 48) => by split <;> first | exact cap_pos j | exact le_rfl) (mem_range.mpr hj)
    simpa only [if_pos hmem] using hs
  calc
    (∑ z ∈ S, log (p z)) ≤ _ := sum_le_sum point
    _ = ∑ j ∈ range 48, ((bin j).card : ℝ)*cap j := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j hj
      rw [← sum_filter]
      have filt : S.filter (fun z => z ∈ bin j) = bin j := by
        ext z
        simp [bin]
      simp [filt]
    _ ≤ ∑ j ∈ range 48, ((allowance j : ℝ)*h)*cap j := by
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (counts j (mem_range.mp hj)) (cap_pos j)
    _ = ((∑ j ∈ range 48, edge (j+1)*allowance j : ℚ) : ℝ)*h*log n := by
      push_cast
      simp only [sum_mul]
      apply sum_congr rfl
      intro j _
      dsimp [cap]
      ring
    _ ≤ _ := by
      have H := budget
      have R : (∑ j ∈ range 48, edge (j+1)*allowance j : ℚ) ≤ 5/9-1/2500 := by linarith
      have R' : ((∑ j ∈ range 48, edge (j+1)*allowance j : ℚ):ℝ) ≤ 5/9-1/2500 := by
        have v := (Rat.cast_le (K := ℝ)).mpr R
        norm_num at v ⊢
        exact v
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right R' (Nat.cast_nonneg _))
        (Real.log_natCast_nonneg _)

end PrimeBlockMesh
#print axioms PrimeBlockMesh.first_power_mass
