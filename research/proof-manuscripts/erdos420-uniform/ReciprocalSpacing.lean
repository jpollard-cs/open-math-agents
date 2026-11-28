import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Spacing of the successive increments of a reciprocal phase.
The phase Y/j has positive downward increments Y/(j(j+1)). On a factor-three
interval they decrease at a controlled rate. The counting results bound
indices at which the increment approaches an integer, as needed in a
second-derivative estimate for exponential sums. -/

noncomputable section
open Finset
namespace ReciprocalSpacing

/-- The downward increment of the phase from j to j+1. -/
def gap (Y : ℝ) (j : ℕ) : ℝ := Y / ((j : ℝ) * (j+1))

theorem phase_sub_phase {Y : ℝ} {j : ℕ} (hj : 0 < j) :
    Y/(j:ℝ) - Y/((j:ℝ)+1) = gap Y j := by
  have jp : (0:ℝ) < j := by exact_mod_cast hj
  unfold gap
  field_simp
  ring

/-- A lower bound for the separation per index, valid on [M,3M]. -/
def step (Y : ℝ) (M : ℕ) : ℝ := 2*Y/(3*(M:ℝ)+1)^3

theorem step_pos {Y : ℝ} (hY : 0 < Y) (M : ℕ) : 0 < step Y M := by
  unfold step
  positivity

theorem separation {Y : ℝ} {M j k : ℕ} (hY : 0 ≤ Y)
    (hM : 1 ≤ M) (hj : M ≤ j) (hjk : j ≤ k) (hk : k ≤ 3*M) :
    ((k:ℝ)-j) * step Y M ≤ gap Y j-gap Y k := by
  have jp : (0:ℝ)<j := by exact_mod_cast (show 0<j by omega)
  have kp : (0:ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have jkle : (j:ℝ) ≤ k := by exact_mod_cast hjk
  have kcap : (k:ℝ) ≤ 3*(M:ℝ) := by exact_mod_cast hk
  let L : ℝ := 3*(M:ℝ)+1
  have Lp : 0 < L := by dsimp [L]; positivity
  have c₁ : (j+1:ℝ)*(k:ℝ)*((k:ℝ)+1) ≤ L^3 := by
    rw [pow_succ, sq]
    gcongr <;> dsimp [L] <;> linarith
  have c₂ : (j:ℝ)*((j:ℝ)+1)*(k:ℝ) ≤ L^3 := by
    rw [pow_succ, sq]
    gcongr <;> dsimp [L] <;> linarith
  have a := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num)
    (show 0 < ((j:ℝ)+1)*k*((k:ℝ)+1) by positivity) c₁
  have b := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1 by norm_num)
    (show 0 < (j:ℝ)*((j:ℝ)+1)*k by positivity) c₂
  calc
    _ = (Y*((k:ℝ)-j))*(1/L^3+1/L^3) := by unfold step; dsimp [L]; ring
    _ ≤ (Y*((k:ℝ)-j))*(1/(((j:ℝ)+1)*k*((k:ℝ)+1))+
        1/((j:ℝ)*((j:ℝ)+1)*k)) :=
      mul_le_mul_of_nonneg_left (add_le_add a b) (mul_nonneg hY (sub_nonneg.mpr jkle))
    _ = _ := by unfold gap; field_simp; ring

theorem gap_le {Y : ℝ} {M j : ℕ} (hY : 0 ≤ Y) (hM : 1 ≤ M) (hj : M ≤ j) :
    gap Y j ≤ Y/(M:ℝ)^2 := by
  have Mp : (0:ℝ)<M := by exact_mod_cast hM
  have jr : (M:ℝ) ≤ j := by exact_mod_cast hj
  unfold gap
  apply div_le_div_of_nonneg_left hY (sq_pos_of_pos Mp)
  rw [sq]
  gcongr
  linarith

/-- Indices at which the increment lies within η of a specified center. -/
def near (Y η k : ℝ) (M : ℕ) : Finset ℕ :=
  (Icc M (3*M)).filter fun j => |gap Y j-k| < η

/-- An arbitrary center catches at most 1+2η/step indices. -/
theorem near_card {Y η k : ℝ} {M : ℕ} (hY : 0 < Y) (hη : 0 ≤ η) (hM : 1 ≤ M) :
    ((near Y η k M).card:ℝ) ≤ 1+2*η/step Y M := by
  let S := near Y η k M
  have sp := step_pos hY M
  by_cases hs : S.Nonempty
  · let a := S.min' hs
    let b := S.max' hs
    have ha : a ∈ S := min'_mem S hs
    have hb : b ∈ S := max'_mem S hs
    have hab : a ≤ b := le_max' S a ha
    have ain := mem_filter.mp (show a ∈ near Y η k M from ha)
    have bin := mem_filter.mp (show b ∈ near Y η k M from hb)
    have sep := separation hY.le hM (mem_Icc.mp ain.1).1 hab (mem_Icc.mp bin.1).2
    have top := (abs_lt.mp ain.2).2
    have bot := (abs_lt.mp bin.2).1
    have width : (b:ℝ)-a ≤ 2*η/step Y M := (le_div_iff₀ sp).mpr (by linarith)
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
def centers (Y η : ℝ) (M : ℕ) : Finset ℤ := Icc 0 ⌊Y/(M:ℝ)^2+η⌋

theorem center_mem {Y η : ℝ} {k : ℤ} {M j : ℕ} (hY : 0 ≤ Y) (hM : 1 ≤ M)
    (hη : η ≤ 1) (hj : M ≤ j) (hd : |gap Y j-(k:ℝ)| < η) :
    k ∈ centers Y η M := by
  obtain ⟨lo,hi⟩ := abs_lt.mp hd
  have gnon : 0 ≤ gap Y j := by unfold gap; positivity
  have neg : (-1:ℝ) < k := by linarith
  have nonneg : (0:ℤ) ≤ k := by
    have h : (-1:ℤ) < k := by exact_mod_cast neg
    omega
  exact mem_Icc.mpr ⟨nonneg,Int.le_floor.mpr (by linarith [gap_le hY hM hj])⟩

theorem centers_card {Y η : ℝ} (hY : 0 ≤ Y) (hη : 0 ≤ η) (M : ℕ) :
    ((centers Y η M).card:ℝ) ≤ Y/(M:ℝ)^2+η+1 := by
  let R := Y/(M:ℝ)^2+η
  have hR : 0 ≤ R := by dsimp [R]; positivity
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
def resonant (Y η : ℝ) (M : ℕ) : Finset ℕ :=
  (Icc M (3*M)).filter fun j => ∃ k : ℤ, |gap Y j-(k:ℝ)| < η

theorem resonant_card {Y η : ℝ} {M : ℕ} (hY : 0 < Y) (hM : 1 ≤ M)
    (hη : 0 ≤ η) (hη' : η ≤ 1) :
    ((resonant Y η M).card : ℝ) ≤
      (Y/(M:ℝ)^2+η+1)*(1+2*η/step Y M) := by
  classical
  let C := centers Y η M
  let S := fun k : ℤ => near Y η (k:ℝ) M
  have sub : resonant Y η M ⊆ C.biUnion S := by
    intro j hj
    obtain ⟨mem,⟨k,hk⟩⟩ := mem_filter.mp hj
    exact mem_biUnion.mpr ⟨k,center_mem hY.le hM hη' (mem_Icc.mp mem).1 hk,
      mem_filter.mpr ⟨mem,hk⟩⟩
  have nbound := (card_le_card sub).trans (card_biUnion_le (s:=C) (t:=S))
  have rbound : ((resonant Y η M).card:ℝ) ≤ ∑ k ∈ C, ((S k).card:ℝ) := by exact_mod_cast nbound
  calc
    _ ≤ _ := rbound
    _ ≤ ∑ _k ∈ C,(1+2*η/step Y M) := sum_le_sum fun k _ => near_card (k:=(k:ℝ)) hY hη hM
    _ = (C.card:ℝ)*(1+2*η/step Y M) := by simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (centers_card hY.le hη M) (by
      have := step_pos hY M
      positivity)


/-- Sum on an interval, given cancellation on every smaller interval in a
single safe cell of the increment. The cells left after removing near-integer
gaps are intervals because the gaps decrease. -/
theorem block_of_safe_cells {Y η K : ℝ} {M a b : ℕ} (hY : 0 < Y) (hM : 1 ≤ M)
    (ha : M ≤ a) (hb : b ≤ 3*M) (hη : 0 < η) (hη' : η ≤ 1) (hK : 0 ≤ K)
    (F : ℕ → ℂ) (unit : ∀ j, ‖F j‖ ≤ 1)
    (safe : ∀ c d : ℕ, a ≤ c → c ≤ d → d ≤ b → ∀ k : ℤ,
      (∀ j ∈ Icc c d, (k:ℝ)+η ≤ gap Y j ∧ gap Y j ≤ (k:ℝ)+1-η) →
      ‖∑ j ∈ Icc c d,F j‖ ≤ K) :
    ‖∑ j ∈ Icc a b,F j‖ ≤
      (Y/(M:ℝ)^2+η+1)*(1+2*η/step Y M + K) := by
  classical
  let U := Icc a b
  let B := U.filter fun j => ∃ k : ℤ, |gap Y j-(k:ℝ)| < η
  let G := U.filter fun j => ¬∃ k : ℤ, |gap Y j-(k:ℝ)| < η
  let C := centers Y η M
  let S (k : ℤ) := G.filter fun j => ⌊gap Y j⌋ = k
  have bounds {j : ℕ} (hj : j ∈ U) := mem_Icc.mp hj
  have badSub : B ⊆ resonant Y η M := by
    intro j hj
    obtain ⟨hj,hd⟩ := mem_filter.mp hj
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨ha.trans (bounds hj).1,(bounds hj).2.trans hb⟩,hd⟩
  have Gmap (j : ℕ) (hj : j ∈ G) : ⌊gap Y j⌋ ∈ C := by
    have jm := ha.trans (bounds (mem_filter.mp hj).1).1
    have pos : 0 ≤ gap Y j := by unfold gap; positivity
    apply mem_Icc.mpr
    refine ⟨Int.floor_nonneg.mpr pos,Int.floor_mono ?_⟩
    linarith [gap_le hY.le hM jm]
  have cellBounds {j : ℕ} {k : ℤ} (hj : j ∈ S k) :
      (k:ℝ)+η ≤ gap Y j ∧ gap Y j ≤ (k:ℝ)+1-η := by
    obtain ⟨hg,hf⟩ := mem_filter.mp hj
    have hn := (mem_filter.mp hg).2
    have fl := Int.floor_le (gap Y j)
    have fh := Int.lt_floor_add_one (gap Y j)
    rw [hf] at fl fh
    have h₁ : η ≤ |gap Y j-(k:ℝ)| := le_of_not_gt fun h => hn ⟨k,h⟩
    have h₂ : η ≤ |gap Y j-((k+1:ℤ):ℝ)| := le_of_not_gt fun h => hn ⟨k+1,h⟩
    push_cast at h₂
    rw [abs_of_nonneg (sub_nonneg.mpr fl)] at h₁
    rw [abs_of_nonpos (by linarith : gap Y j - ((k:ℝ)+1) ≤ 0)] at h₂
    constructor <;> linarith
  have makeCell {j : ℕ} {k : ℤ} (hj : j ∈ U)
      (hd : (k:ℝ)+η ≤ gap Y j ∧ gap Y j ≤ (k:ℝ)+1-η) : j ∈ S k := by
    have hf : ⌊gap Y j⌋ = k := Int.floor_eq_iff.mpr ⟨by linarith [hd.1],by linarith [hd.2]⟩
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨hj,?_⟩,hf⟩
    rintro ⟨l,hl⟩
    obtain ⟨low,high⟩ := abs_lt.mp hl
    by_cases e : l ≤ k
    · have er : (l:ℝ) ≤ k := by exact_mod_cast e
      linarith [hd.1]
    · have ei : k+1 ≤ l := by omega
      have er : (k:ℝ)+1 ≤ l := by exact_mod_cast ei
      linarith [hd.2]
  have mono {j k : ℕ} (hj : M ≤ j) (hjk : j ≤ k) (hk : k ≤ 3*M) :
      gap Y k ≤ gap Y j := by
    have sr := separation hY.le hM hj hjk hk
    have le : (0:ℝ) ≤ (k:ℝ)-(j:ℝ) := sub_nonneg.mpr (by exact_mod_cast hjk)
    have nonneg := mul_nonneg le (step_pos hY M).le
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
          (k:ℝ)+η ≤ gap Y j ∧ gap Y j ≤ (k:ℝ)+1-η := by
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
  have bcost : ‖∑ j ∈ B,F j‖ ≤ (resonant Y η M).card := by
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
    _ ≤ ((resonant Y η M).card:ℝ)+(C.card:ℝ)*K := add_le_add bcost gcost
    _ ≤ _ := by
      rw [mul_add]
      exact add_le_add (resonant_card hY hM hη.le hη') (mul_le_mul_of_nonneg_right
        (centers_card hY.le hη.le M) hK)

end ReciprocalSpacing
#print axioms ReciprocalSpacing.separation
#print axioms ReciprocalSpacing.resonant_card
#print axioms ReciprocalSpacing.block_of_safe_cells
