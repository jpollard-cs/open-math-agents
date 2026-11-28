import FormalConjectures.ErdosProblems.«420»
import Mathlib

/-! Geometric limit points and the exact catalog conclusions for the two
density parts of problem 420. The analytic window theorem is an explicit
hypothesis. Codex (AI) at Jordan Pollard's request. -/
noncomputable section
open Filter Set

namespace FactorialDensity

theorem geometric_points {S : Set ℝ}
    (grid : ∀ D r : ℕ, 0 < D → (1+1/(D:ℝ))^r ∈ closure S) :
    Ioi (1:ℝ) ⊆ closure S := by
  intro x hx
  change 1 < x at hx
  rw [← closure_closure (s:=S), Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨d, hd⟩ := exists_nat_gt (x/ε)
  have hd0 : 0 < (d:ℝ) := lt_trans (div_pos (by linarith) hε) hd
  have hdN : 0<d := by exact_mod_cast hd0
  let a := 1+1/(d:ℝ)
  have ha : 1 < a := by dsimp only [a]; have hp := one_div_pos.mpr hd0; linarith only [hp]
  obtain ⟨r,hr,hnext⟩ := exists_nat_pow_near hx.le ha
  refine ⟨a^r,grid d r hdN,?_⟩
  rw [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hr)]
  have gap : x/(d:ℝ)<ε := (div_lt_iff₀ hd0).mpr (by linarith only [(div_lt_iff₀ hε).mp hd])
  rw [pow_succ] at hnext
  change x < a^r * (1+1/(d:ℝ)) at hnext
  rw [mul_add,mul_one,mul_one_div] at hnext
  have bound := div_le_div_of_nonneg_right hr hd0.le
  linarith only [hnext,bound,gap]

/-- Arbitrarily late starting integers realize all window lengths in the
stated range simultaneously. This is the analytic hypothesis. -/
def profiles : Prop := ∀ D r : ℕ, 0 < D → ∃ J : ℕ, ∀ ε : ℝ, 0 < ε →
    ∃ᶠ n : ℕ in atTop, ∀ h : ℕ, J ≤ h → (h:ℝ) ≤ Real.log n →
      dist (Erdos420.F (fun _ => (h:ℝ)) n) ((1+1/(D:ℝ))^r) < ε

theorem all_growing_windows (analytic : profiles) (f : ℕ → ℝ)
    (bound : ∀ n, f n ≤ Real.log n) (grow : Tendsto f atTop atTop) :
    Ioi (1:ℝ) ⊆ closure (Set.range (Erdos420.F f)) := by
  apply geometric_points
  intro D r hD
  obtain ⟨J,realize⟩ := analytic D r hD
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn, large⟩ := ((realize ε hε).and_eventually (grow.eventually_ge_atTop (J:ℝ))).exists
  let h := ⌊f n⌋₊
  have hL : J ≤ h := Nat.le_floor large
  have hU : (h:ℝ) ≤ Real.log n := (Nat.floor_le ((Nat.cast_nonneg J).trans large)).trans (bound n)
  have hit := hn h hL hU
  have eq : Erdos420.F (fun _ => (h:ℝ)) n = Erdos420.F f n := by simp [Erdos420.F,h]
  exact ⟨Erdos420.F f n,⟨n,rfl⟩,by simpa only [eq,dist_comm] using hit⟩

theorem original_iii (analytic : profiles) : type_of% @Erdos420.erdos_420.parts.iii := by
  intro f _ bound grow
  exact all_growing_windows analytic f bound grow

theorem original_ii (analytic : profiles) : type_of% @Erdos420.erdos_420.parts.ii := by
  apply all_growing_windows analytic (fun n : ℕ => Real.log n) (fun _ => le_rfl)
  exact Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

end FactorialDensity
#print axioms FactorialDensity.geometric_points
#print axioms FactorialDensity.original_ii
#print axioms FactorialDensity.original_iii
