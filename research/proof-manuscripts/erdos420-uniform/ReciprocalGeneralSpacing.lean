import ReciprocalFirstDerivative
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! A partition for exponential sums whose consecutive downward increments
decrease by at least a fixed amount per index. The finite argument
splits the resonant increments from the intervals in safe cells. -/
noncomputable section
open Finset
namespace SeparatedGaps
structure Profile where
  gap : ℕ → ℝ
  lo : ℕ
  hi : ℕ
  cap : ℝ
  step : ℝ
  step_pos : 0 < step
  nonneg : ∀ j, 0 ≤ gap j
  gap_le : ∀ {j}, lo ≤ j → gap j ≤ cap
  separation : ∀ {j k : ℕ}, lo ≤ j → j ≤ k → k ≤ hi →
    ((k:ℝ)-j)*step ≤ gap j-gap k

theorem Profile.cap_nonneg (P : Profile) : 0 ≤ P.cap :=
  (P.nonneg P.lo).trans (P.gap_le (j:=P.lo) le_rfl)

variable (P : Profile)

/-- Indices at which the increment lies within η of a specified center. -/
def near (η k : ℝ) : Finset ℕ :=
  (Icc P.lo (P.hi)).filter fun j => |P.gap j-k| < η

/-- An arbitrary center catches at most 1+2η/step indices. -/
lemma near_card {η k : ℝ} (hη : 0 ≤ η) :
    ((near P η k).card:ℝ) ≤ 1+2*η/P.step := by
  let S := near P η k
  have sp := P.step_pos
  by_cases hs : S.Nonempty
  · let a := S.min' hs
    let b := S.max' hs
    have ha : a ∈ S := min'_mem S hs
    have hb : b ∈ S := max'_mem S hs
    have hab : a ≤ b := le_max' S a ha
    have ain := mem_filter.mp (show a ∈ near P η k from ha)
    have bin := mem_filter.mp (show b ∈ near P η k from hb)
    have sep := P.separation (mem_Icc.mp ain.1).1 hab (mem_Icc.mp bin.1).2
    have top := (abs_lt.mp ain.2).2
    have bot := (abs_lt.mp bin.2).1
    have width : (b:ℝ)-a ≤ 2*η/P.step := (le_div_iff₀ sp).mpr (by linarith)
    have subset : S ⊆ Icc a b := fun j hj =>
      mem_Icc.mpr ⟨min'_le S j hj,le_max' S j hj⟩
    have bound := card_le_card subset
    rw [Nat.card_Icc] at bound
    have coeff : ((S.card : ℕ):ℝ) ≤ (b:ℝ)+1-a := by
      exact_mod_cast (show (S.card:ℤ) ≤ (b:ℤ)+1-a by omega)
    change (S.card:ℝ) ≤ _
    linarith
  · have heq : S = ∅ := not_nonempty_iff_eq_empty.mp hs
    change (S.card:ℝ) ≤ _
    rw [heq,card_empty,Nat.cast_zero]
    positivity

/-- A finite interval containing every integer approached by an increment. -/
def centers (η : ℝ) : Finset ℤ := Icc 0 ⌊P.cap+η⌋

lemma center_mem {η : ℝ} {k : ℤ} {j : ℕ}
    (hη : η ≤ 1) (hj : P.lo ≤ j) (hd : |P.gap j-(k:ℝ)| < η) :
    k ∈ centers P η := by
  obtain ⟨lo,hi⟩ := abs_lt.mp hd
  have gnon : 0 ≤ P.gap j := P.nonneg _
  have neg : (-1:ℝ) < k := by linarith
  have nonneg : (0:ℤ) ≤ k := by
    have h : (-1:ℤ) < k := by exact_mod_cast neg
    omega
  exact mem_Icc.mpr ⟨nonneg,Int.le_floor.mpr (by linarith [P.gap_le hj])⟩

lemma centers_card {η : ℝ} (hη : 0 ≤ η) :
    ((centers P η).card:ℝ) ≤ P.cap+η+1 := by
  let R := P.cap+η
  have hR : 0 ≤ R := by dsimp [R]; linarith [P.cap_nonneg]
  have hfl : (0:ℤ) ≤ ⌊R⌋ := Int.floor_nonneg.mpr hR
  change ((Icc (0:ℤ) ⌊R⌋).card:ℝ) ≤ R+1
  rw [Int.card_Icc,sub_zero]
  have h := Int.floor_le R
  have nonneg : 0 ≤ ⌊R⌋ + 1 := by omega
  exact_mod_cast (show (((⌊R⌋ + 1).toNat:ℤ):ℝ) ≤ R+1 by
    rw [Int.toNat_of_nonneg nonneg,Int.cast_add,Int.cast_one]
    linarith)

open scoped Classical in
/-- All near-resonant indices in the factor-three interval. -/
def resonant (η : ℝ) : Finset ℕ :=
  (Icc P.lo (P.hi)).filter fun j => ∃ k : ℤ, |P.gap j-(k:ℝ)| < η

lemma resonant_card {η : ℝ}
    (hη : 0 ≤ η) (hη' : η ≤ 1) :
    ((resonant P η).card : ℝ) ≤
      (P.cap+η+1)*(1+2*η/P.step) := by
  classical
  let C := centers P η
  let S := fun k : ℤ => near P η (k:ℝ)
  have sub : resonant P η ⊆ C.biUnion S := by
    intro j hj
    obtain ⟨mem,⟨k,hk⟩⟩ := mem_filter.mp hj
    exact mem_biUnion.mpr ⟨k,center_mem P hη' (mem_Icc.mp mem).1 hk,
      mem_filter.mpr ⟨mem,hk⟩⟩
  have nbound := (card_le_card sub).trans (card_biUnion_le (s:=C) (t:=S))
  have rbound : ((resonant P η).card:ℝ) ≤ ∑ k ∈ C, ((S k).card:ℝ) := by exact_mod_cast nbound
  calc
    _ ≤ _ := rbound
    _ ≤ ∑ _k ∈ C,(1+2*η/P.step) := sum_le_sum fun k _ => near_card P (k:=(k:ℝ)) hη
    _ = (C.card:ℝ)*(1+2*η/P.step) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (centers_card P hη) (by
      have := P.step_pos
      positivity)


/-- Sum on an interval, given cancellation on every smaller interval in a
single safe cell of the increment. The cells left after removing near-integer
gaps are intervals because the gaps decrease. -/
lemma block_of_safe_cells {η K : ℝ} {a b : ℕ}
    (ha : P.lo ≤ a) (hb : b ≤ P.hi) (hη : 0 < η) (hη' : η ≤ 1) (hK : 0 ≤ K)
    (F : ℕ → ℂ) (unit : ∀ j, ‖F j‖ ≤ 1)
    (safe : ∀ c d : ℕ, a ≤ c → c ≤ d → d ≤ b → ∀ k : ℤ,
      (∀ j ∈ Icc c d, (k:ℝ)+η ≤ P.gap j ∧ P.gap j ≤ (k:ℝ)+1-η) →
      ‖∑ j ∈ Icc c d,F j‖ ≤ K) :
    ‖∑ j ∈ Icc a b,F j‖ ≤
      (P.cap+η+1)*(1+2*η/P.step + K) := by
  classical
  let U := Icc a b
  let B := U.filter fun j => ∃ k : ℤ, |P.gap j-(k:ℝ)| < η
  let G := U.filter fun j => ¬∃ k : ℤ, |P.gap j-(k:ℝ)| < η
  let C := centers P η
  let S (k : ℤ) := G.filter fun j => ⌊P.gap j⌋ = k
  have bounds {j : ℕ} (hj : j ∈ U) := mem_Icc.mp hj
  have badSub : B ⊆ resonant P η := by
    intro j hj
    obtain ⟨hj,hd⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨ha.trans (bounds hj).1,(bounds hj).2.trans hb⟩,hd⟩
  have Gmap (j : ℕ) (hj : j ∈ G) : ⌊P.gap j⌋ ∈ C := by
    have jm := ha.trans (bounds (mem_filter.mp hj).1).1
    have pos : 0 ≤ P.gap j := P.nonneg _
    apply mem_Icc.mpr
    refine ⟨Int.floor_nonneg.mpr pos,Int.floor_mono ?_⟩
    linarith [P.gap_le jm]
  have cellBounds {j : ℕ} {k : ℤ} (hj : j ∈ S k) :
      (k:ℝ)+η ≤ P.gap j ∧ P.gap j ≤ (k:ℝ)+1-η := by
    obtain ⟨hg,hf⟩ := mem_filter.mp hj
    have hn := (mem_filter.mp hg).2
    have fl := Int.floor_le (P.gap j)
    have fh := Int.lt_floor_add_one (P.gap j)
    rw [hf] at fl fh
    have h₁ : η ≤ |P.gap j-(k:ℝ)| := le_of_not_gt fun h => hn ⟨k,h⟩
    have h₂ : η ≤ |P.gap j-((k+1:ℤ):ℝ)| := le_of_not_gt fun h => hn ⟨k+1,h⟩
    push_cast at h₂
    rw [abs_of_nonneg (sub_nonneg.mpr fl)] at h₁
    rw [abs_of_nonpos (by linarith : P.gap j - ((k:ℝ)+1) ≤ 0)] at h₂
    constructor <;> linarith
  have makeCell {j : ℕ} {k : ℤ} (hj : j ∈ U)
      (hd : (k:ℝ)+η ≤ P.gap j ∧ P.gap j ≤ (k:ℝ)+1-η) : j ∈ S k := by
    have hf : ⌊P.gap j⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith [hd.1],by linarith [hd.2]⟩
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hj,?_⟩,hf⟩
    rintro ⟨l,hl⟩
    obtain ⟨low,high⟩ := abs_lt.mp hl
    by_cases e : l ≤ k
    · have er : (l:ℝ) ≤ k := by exact_mod_cast e
      linarith [hd.1]
    · have ei : k+1 ≤ l := by omega
      have er : (k:ℝ)+1 ≤ l := by exact_mod_cast ei
      linarith [hd.2]
  have mono {j k : ℕ} (hj : P.lo ≤ j) (hjk : j ≤ k) (hk : k ≤ P.hi) :
      P.gap k ≤ P.gap j := by
    have sr := P.separation hj hjk hk
    have le : (0:ℝ) ≤ (k:ℝ)-(j:ℝ) := sub_nonneg.mpr (by exact_mod_cast hjk)
    have nonneg := mul_nonneg le (P.step_pos).le
    linarith
  have sumcell (k : ℤ) : ‖∑ j ∈ S k,F j‖ ≤ K := by
    by_cases hs : (S k).Nonempty
    · let c := (S k).min' hs
      let d := (S k).max' hs
      have cm : c ∈ S k := min'_mem _ _
      have dm : d ∈ S k := max'_mem _ _
      have cu := bounds (mem_filter.mp (mem_filter.mp cm).1).1
      have du := bounds (mem_filter.mp (mem_filter.mp dm).1).1
      have cd : c ≤ d := le_max' _ _ cm
      have between (j : ℕ) (hj : j ∈ Icc c d) :
          (k:ℝ)+η ≤ P.gap j ∧ P.gap j ≤ (k:ℝ)+1-η := by
        obtain ⟨jl,jr⟩ := mem_Icc.mp hj
        have low := mono (ha.trans (cu.1.trans jl)) jr (du.2.trans hb)
        have high := mono (ha.trans cu.1) jl (jr.trans (du.2.trans hb))
        exact ⟨(cellBounds dm).1.trans low, high.trans (cellBounds cm).2⟩
      have eq : S k = Icc c d := by
        ext j
        constructor
        · intro hj
          exact mem_Icc.mpr ⟨min'_le _ _ hj,le_max' _ _ hj⟩
        · intro hj
          exact makeCell (mem_Icc.mpr ⟨cu.1.trans (mem_Icc.mp hj).1,(mem_Icc.mp hj).2.trans du.2⟩)
            (between j hj)
      rw [eq]
      exact safe c d cu.1 cd du.2 k between
    · rw [not_nonempty_iff_eq_empty.mp hs]
      simpa using hK
  have decomp : ∑ j ∈ B,F j + ∑ j ∈ G,F j = ∑ j ∈ U,F j :=
    sum_filter_add_sum_filter_not _ _ _
  have partition : ∑ k ∈ C,∑ j ∈ S k,F j = ∑ j ∈ G,F j :=
    Finset.sum_fiberwise_of_maps_to Gmap F
  have bcost : ‖∑ j ∈ B,F j‖ ≤ (resonant P η).card := by
    calc _ ≤ ∑ j ∈ B,‖F j‖ := norm_sum_le _ _
         _ ≤ ∑ _j ∈ B,(1:ℝ) := sum_le_sum fun j _ => unit j
         _ = B.card := by simp
         _ ≤ _ := by exact_mod_cast card_le_card badSub
  have gcost : ‖∑ j ∈ G,F j‖ ≤ (C.card:ℝ)*K := by
    rw [← partition]
    calc _ ≤ ∑ k ∈ C,‖∑ j ∈ S k,F j‖ := norm_sum_le _ _
         _ ≤ ∑ _k ∈ C,K := sum_le_sum fun k _ => sumcell k
         _ = _ := by simp
  rw [← decomp]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ ((resonant P η).card:ℝ)+(C.card:ℝ)*K := add_le_add bcost gcost
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (resonant_card P hη.le hη') (mul_le_mul_of_nonneg_right
        (centers_card P hη.le) hK)

/-- A van der Corput block estimate for any phase with a bounded, separated
profile of nonnegative, decreasing downward increments. -/
theorem phase_block {a b : ℕ} {η : ℝ} (ha : P.lo ≤ a) (hb : b ≤ P.hi)
    (hη : 0 < η) (hη' : η ≤ 1) (phase : ℕ → ℝ)
    (diff : ∀ j, phase (j+1) - phase j = -P.gap j) :
    ‖∑ j ∈ Icc a b, ReciprocalFirstDerivative.wave (phase j)‖ ≤
      (P.cap+η+1)*(1+2*η/P.step + (1+1/η)) := by
  apply block_of_safe_cells P ha hb hη hη' (by positivity) _ (by simp)
  intro c d ac cd db k band
  let f (j : ℕ) : ℝ := phase (c+j)
  have decr (j : ℕ) : f (j+1)-f j = -P.gap (c+j) := by
    simpa only [f,← Nat.add_assoc] using diff (c+j)
  have inc (j : ℕ) (hj : j < d-c) : f (j+1)-f j ≤ f (j+2)-f (j+1) := by
    rw [decr j,decr (j+1),neg_le_neg_iff]
    have sep := P.separation (j:=c+j) (k:=c+(j+1)) (by omega) (by omega) (by omega)
    have nonneg : 0 ≤ ((c+(j+1):ℕ):ℝ)-((c+j:ℕ):ℝ) := sub_nonneg.mpr
      (by exact_mod_cast (show c+j ≤ c+(j+1) by omega))
    linarith [mul_nonneg nonneg P.step_pos.le]
  have safe (j : ℕ) (hj : j ≤ d-c) :
      ((-k-1:ℤ):ℝ)+η ≤ f (j+1)-f j ∧ f (j+1)-f j ≤ ((-k-1:ℤ):ℝ)+1-η := by
    have bj := band (c+j) (mem_Icc.mpr ⟨by omega,by omega⟩)
    rw [decr]
    push_cast
    constructor <;> linarith [bj.1,bj.2]
  have h := ReciprocalFirstDerivative.first_difference_bound f (d-c) (-k-1) hη safe inc
  rw [← Ico_add_one_right_eq_Icc,Finset.sum_Ico_eq_sum_range,show d+1-c = d-c+1 by omega]
  simpa only [f, Nat.add_comm] using h

/-- In the middle-frequency range the generic block estimate has square-root
size. The coefficient K measures the ratio between the largest downward gap
and its guaranteed decrease over M indices. -/
theorem middle_frequency {a b : ℕ} {M K : ℝ} (ha : P.lo ≤ a) (hb : b ≤ P.hi)
    (hM : 0 < M) (hK : 0 < K) (hcap : 1/2 ≤ P.cap) (upper : P.cap ≤ M)
    (curvature : P.cap/(K*M) ≤ P.step) (phase : ℕ → ℝ)
    (diff : ∀ j, phase (j+1)-phase j = -P.gap j) :
    ‖∑ j ∈ Icc a b, ReciprocalFirstDerivative.wave (phase j)‖ ≤
      5*(3+2*K)*Real.sqrt (M*P.cap) := by
  let d := Real.sqrt (P.cap/M)
  have cp : 0 < P.cap := by linarith
  have dp : 0 < d := Real.sqrt_pos.mpr (div_pos cp hM)
  have ds : d^2 = P.cap/M := Real.sq_sqrt (div_nonneg cp.le hM.le)
  have d1 : d ≤ 1 := by
    have hh := (div_le_one hM).mpr upper
    nlinarith
  have raw := phase_block P ha hb dp d1 phase diff
  have h₁ : P.cap+d+1 ≤ 5*P.cap := by linarith
  have sstep := (div_le_iff₀ (mul_pos hK hM)).mp curvature
  have ident := (eq_div_iff hM.ne').mp ds
  have cost : 2*d/P.step ≤ 2*K/d := by
    apply (div_le_div_iff₀ P.step_pos dp).mpr
    have cmp : d^2 ≤ P.step*K := (mul_le_mul_iff_left₀ hM).mp (by linarith [show P.step*(K*M)=P.step*K*M by ring])
    nlinarith
  have h₂ : 1+2*d/P.step+(1+1/d) ≤ (3+2*K)/d := by
    have one : 1 ≤ 1/d := (one_le_div dp).mpr d1
    rw [add_div]
    linarith [show (3:ℝ)/d=3*(1/d) by ring]
  have sp := P.step_pos
  have hh := mul_le_mul h₁ h₂ (by positivity) (by positivity)
  apply raw.trans (hh.trans ?_)
  have r : Real.sqrt (M*P.cap) = M*d := by
    have ms : (M*d)^2 = M*P.cap := by
      calc (M*d)^2 = M*(d^2*M) := by ring
           _ = _ := by rw [ident]
    rw [← ms, Real.sqrt_sq (mul_nonneg hM.le dp.le)]
  have cd : P.cap/d = M*d := (div_eq_iff dp.ne').mpr (by rw [← ident]; ring)
  rw [r]
  apply le_of_eq
  calc 5*P.cap*((3+2*K)/d) = 5*(3+2*K)*(P.cap/d) := by ring
       _ = _ := by rw [cd]

end SeparatedGaps
#print axioms SeparatedGaps.block_of_safe_cells
#print axioms SeparatedGaps.phase_block
#print axioms SeparatedGaps.middle_frequency
