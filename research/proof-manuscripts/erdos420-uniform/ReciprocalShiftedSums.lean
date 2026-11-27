import ReciprocalMixedDifferences
import ReciprocalFirstDerivative

/-! Cancellation in a nonresonant strip after any number of reciprocal
differencing steps. The inverse-frequency constant retains the product
of all shifts. -/
noncomputable section
open Finset ReciprocalFirstDerivative
namespace FactorialReciprocal

/-- An explicit low-frequency bound for every mixed difference of 1/x.
With m shifts, its effective first difference has scale C (m+1)! prod(h) / B^(m+2).
The hypothesis is that the largest such difference is at most one half. -/
theorem shifted_low_frequency (hs : List ℝ) (N : ℕ) {C B : ℝ} (hB : 0 < B)
    (hC : 0 ≤ C) (hn : ∀ a ∈ hs, 0 ≤ a)
    (pos : 0 < C * ((hs.length+1).factorial : ℝ) * hs.prod)
    (small : 2*(C * ((hs.length+1).factorial : ℝ) * hs.prod) ≤ B^(hs.length+2)) :
    ‖∑ j ∈ range (N+1), wave (C * diffPow hs 1 (B+j))‖ ≤
      1+(B+N+1+hs.sum)^(hs.length+2)/(C*((hs.length+1).factorial : ℝ)*hs.prod) := by
  let S := C*((hs.length+1).factorial : ℝ)*hs.prod
  let W := B+N+1+hs.sum
  let a (j : ℕ) := C*diffPow (1::hs) 1 (B+j)
  let δ := S/W^(hs.length+2)
  have hh : ∀ y ∈ ((1:ℝ)::hs), 0 ≤ y := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl|h
    · norm_num
    · exact hn _ h
  have sumh := List.sum_nonneg hn
  have wpos : 0 < W := by dsimp [W]; positivity
  have δpos : 0 < δ := div_pos pos (pow_pos wpos _)
  have ant : Antitone a := by
    intro i j hij
    have e : (i:ℝ) ≤ j := by exact_mod_cast hij
    exact mul_le_mul_of_nonneg_left (diffPow_antitoneOn (1::hs) 1 hh
      (show 0 < B+i by positivity) (show 0 < B+j by positivity) (by linarith)) hC
  have low : δ ≤ a N := by
    have h := (diffPow_bounds (1::hs) 1 (show 0 < B+N by positivity) hh).1
    have v := mul_le_mul_of_nonneg_left h hC
    simp only [List.length_cons,Nat.one_ascFactorial,List.prod_cons,one_mul,
      List.sum_cons,show 1+(hs.length+1)=hs.length+2 by omega] at v
    rw [← mul_div_assoc, ← mul_assoc, show B+N+(1+hs.sum)=W by dsimp [W]; ring] at v
    exact v
  have high : a 0 ≤ 1/2 := by
    have h := (diffPow_bounds (1::hs) 1 hB hh).2
    have v := mul_le_mul_of_nonneg_left h hC
    simp only [List.length_cons,Nat.one_ascFactorial,List.prod_cons,one_mul,
      show 1+(hs.length+1)=hs.length+2 by omega] at v
    rw [← mul_div_assoc, ← mul_assoc] at v
    have cap : S/B^(hs.length+2) ≤ 1/2 := (div_le_iff₀ (pow_pos hB _)).mpr (by dsimp [S]; linarith)
    simpa [a] using v.trans cap
  have gap (j : ℕ) : C*diffPow hs 1 (B+(j+1 : ℕ))-C*diffPow hs 1 (B+j) = -(a j) := by
    simp only [Nat.cast_add,Nat.cast_one,a,diffPow,← add_assoc]
    ring
  have bound := first_difference_bound (fun j => C*diffPow hs 1 (B+j)) N (-1) δpos (by
    intro j hj
    simp only [gap,Int.cast_neg,Int.cast_one]
    have ah := (ant (Nat.zero_le j)).trans high
    have dl := low.trans (ant hj)
    constructor <;> linarith) (by
    intro j _
    rw [gap j,gap (j+1),neg_le_neg_iff]
    exact ant (Nat.le_succ j))
  convert bound using 2
  dsimp [δ,S,W]
  rw [one_div_div]

end FactorialReciprocal
#print axioms FactorialReciprocal.shifted_low_frequency
