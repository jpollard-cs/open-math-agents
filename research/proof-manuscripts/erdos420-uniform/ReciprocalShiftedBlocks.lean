import ReciprocalMixedDifferences
import ReciprocalGeneralSpacing

/-! An explicit second-derivative block estimate after arbitrary reciprocal
differencing shifts, specialized to a finite interval of indices. -/
noncomputable section
open Finset ReciprocalFirstDerivative
namespace FactorialReciprocal

/-- Gap profile for all indices between 0 and N after a list of positive shifts. -/
def shiftedProfile (hs : List ℝ) (N : ℕ) {C B : ℝ} (hB : 0 < B)
    (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) : SeparatedGaps.Profile := by
  let g (j : ℕ) := C * diffPow (1::hs) 1 (B+j)
  let A := C*((hs.length+1).factorial : ℝ)*hs.prod / B^(hs.length+2)
  let K := C*((hs.length+2).factorial : ℝ)*hs.prod
  let L := K/(B+N+1+hs.sum)^(hs.length+3)
  have hsn : ∀ t ∈ hs, 0 ≤ t := fun t ht => (hn t ht).le
  have hp := List.prod_pos hn
  have hsum := List.sum_nonneg hsn
  have hkp : 0 < K := by dsimp [K]; positivity
  have hlp : 0 < L := by dsimp [L]; positivity
  have gt : ∀ t ∈ ((1:ℝ)::hs), 0 ≤ t := List.forall_mem_cons.mpr ⟨by norm_num,hsn⟩
  have gcap (j : ℕ) : g j ≤ A := by
    have e := (diffPow_bounds (1::hs) 1 (show 0 < B+j by positivity) gt).2
    have ce := mul_le_mul_of_nonneg_left e hC.le
    simp only [List.length_cons,Nat.one_ascFactorial,List.prod_cons,one_mul,
      show 1+(hs.length+1)=hs.length+2 by omega] at ce
    rw [← mul_div_assoc, ← mul_assoc] at ce
    apply ce.trans
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    apply pow_le_pow_left₀ hB.le
    exact le_add_of_nonneg_right (Nat.cast_nonneg j)
  have sep {j k : ℕ} (jk : j ≤ k) (kn : k ≤ N) : ((k:ℝ)-j)*L ≤ g j-g k := by
    let d : ℝ := (k:ℝ)-j
    have d0 : 0 ≤ d := sub_nonneg.mpr (by exact_mod_cast jk)
    have hh : ∀ t ∈ (d::1::hs), 0 ≤ t := List.forall_mem_cons.mpr ⟨d0,gt⟩
    have e := (diffPow_bounds (d::1::hs) 1 (show 0 < B+j by positivity) hh).1
    have ce := mul_le_mul_of_nonneg_left e hC.le
    have idx : B+j+d=B+k := by dsimp [d]; ring
    have ix : B+j+(d+(1+hs.sum)) = B+k+1+hs.sum := by dsimp [d]; ring
    simp only [List.length_cons,Nat.one_ascFactorial,List.prod_cons,one_mul,
      List.sum_cons,show 1+(hs.length+1+1)=hs.length+3 by omega,ix] at ce
    change _ ≤ C * (diffPow (1::hs) 1 (B+j)-diffPow (1::hs) 1 (B+j+d)) at ce
    rw [idx, mul_sub] at ce
    apply le_trans _ ce
    rw [← mul_div_assoc C]
    have coeff : C*((hs.length+1+1).factorial * (d*hs.prod)) = d*K := by dsimp [K]; ring
    rw [coeff]
    change d*(K / _) ≤ d*K/_
    rw [mul_div_assoc d K]
    apply mul_le_mul_of_nonneg_left _ d0
    apply div_le_div_of_nonneg_left hkp.le (by positivity)
    apply pow_le_pow_left₀ (by positivity)
    have kh : (k:ℝ) ≤ N := by exact_mod_cast kn
    linarith
  exact {
    gap := g
    lo := 0
    hi := N
    cap := A
    step := L
    step_pos := hlp
    nonneg := fun j => mul_nonneg hC.le (diffPow_nonneg (1::hs) 1 (by positivity) gt)
    gap_le := fun {j} _ => gcap j
    separation := fun _ jk kn => sep jk kn
  }

private theorem mixed_increment (hs : List ℝ) (C B : ℝ) (j : ℕ) :
    C * diffPow hs 1 (B+(j+1 : ℕ)) - C * diffPow hs 1 (B+j) =
      -(C * diffPow (1::hs) 1 (B+j)) := by
  simp only [Nat.cast_add,Nat.cast_one,diffPow,← add_assoc]
  ring

/-- The optimal endpoints from two mixed reciprocal differences supply
a gap profile for the exponential-sum estimate. -/
theorem shifted_phase_block (hs : List ℝ) (N a b : ℕ) {C B η : ℝ} (hB : 0 < B)
    (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) (hb : b ≤ N) (hη : 0 < η) (hη' : η ≤ 1) :
    let A := C*((hs.length+1).factorial : ℝ)*hs.prod / B^(hs.length+2)
    let L := C*((hs.length+2).factorial : ℝ)*hs.prod / (B+N+1+hs.sum)^(hs.length+3)
    ‖∑ j ∈ Icc a b,wave (C*diffPow hs 1 (B+j))‖ ≤
      (A+η+1)*(1+2*η/L+(1+1/η)) := by
  let P := shiftedProfile hs N hB hC hn
  apply SeparatedGaps.phase_block P (Nat.zero_le a) hb hη hη'
  exact mixed_increment hs C B

/-- Square-root cancellation in the regular frequency range of every shifted reciprocal phase.
The spacing ratio K is separated from the numerical endpoints of the block. -/
theorem shifted_middle_frequency (hs : List ℝ) (N a b : ℕ) {C B M K : ℝ}
    (hB : 0 < B) (hC : 0 < C) (hn : ∀ t ∈ hs, 0 < t) (hb : b ≤ N)
    (hM : 0 < M) (hK : 0 < K)
    (lower : 1/2 ≤ (shiftedProfile hs N hB hC hn).cap)
    (upper : (shiftedProfile hs N hB hC hn).cap ≤ M)
    (curvature : (shiftedProfile hs N hB hC hn).cap/(K*M) ≤ (shiftedProfile hs N hB hC hn).step) :
    ‖∑ j ∈ Icc a b,wave (C*diffPow hs 1 (B+j))‖ ≤
      5*(3+2*K)*Real.sqrt (M*(shiftedProfile hs N hB hC hn).cap) := by
  apply SeparatedGaps.middle_frequency (shiftedProfile hs N hB hC hn) (Nat.zero_le a)
    hb hM hK lower upper curvature
  exact mixed_increment hs C B

end FactorialReciprocal
#print axioms FactorialReciprocal.shifted_phase_block
#print axioms FactorialReciprocal.shifted_middle_frequency
