import Init

/-! A finite averaging bound for failures of divisibility by a fixed modulus. -/

namespace SeedAverage

/-- Sum over the half-open interval starting at `a` with length `n`. -/
def intervalSum (f : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => intervalSum f a n + f (a+n)

theorem intervalSum_add (f : Nat → Nat) (a m n : Nat) :
    intervalSum f a (m+n) = intervalSum f a m + intervalSum f (a+m) n := by
  induction n with
  | zero => simp [intervalSum]
  | succ n ih => simp [intervalSum, ih, Nat.add_assoc]

theorem intervalSum_mono_length (f : Nat → Nat) {a m n : Nat} (h : m ≤ n) :
    intervalSum f a m ≤ intervalSum f a n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [intervalSum_add]
  omega

theorem shifted_sum_le (f : Nat → Nat) (a d n : Nat) :
    intervalSum f (a+d) n ≤ intervalSum f a (d+n) := by
  rw [intervalSum_add]
  omega

theorem intervalSum_pointwise_add (f g : Nat → Nat) (a n : Nat) :
    intervalSum (fun i => f i + g i) a n = intervalSum f a n + intervalSum g a n := by
  induction n with
  | zero => simp [intervalSum]
  | succ n ih => simp only [intervalSum, ih]; omega

theorem intervalSum_shift (f : Nat → Nat) (a d n : Nat) :
    intervalSum (fun i => f (i+d)) a n = intervalSum f (a+d) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [intervalSum, ih, Nat.add_right_comm a n d]

theorem sum_of_windows_le (f : Nat → Nat) (a n h : Nat) :
    intervalSum (fun t => intervalSum f t h) a n ≤ h * intervalSum f a (n+h) := by
  induction h with
  | zero =>
    simp only [intervalSum, Nat.zero_mul]
    induction n with
    | zero => simp [intervalSum]
    | succ n ih => simpa [intervalSum] using ih
  | succ h ih =>
    change intervalSum (fun t => intervalSum f t h + f (t+h)) a n ≤ _
    rw [intervalSum_pointwise_add, intervalSum_shift]
    have tail := shifted_sum_le f a h n
    have mono := intervalSum_mono_length f (a := a) (m := n+h) (n := n+(h+1)) (by omega)
    have first := Nat.mul_le_mul_left h mono
    rw [Nat.succ_mul]
    exact Nat.add_le_add (Nat.le_trans ih first) (Nat.le_trans (by simpa [Nat.add_comm h n] using tail) mono)

theorem constant_lower (f : Nat → Nat) (a n b : Nat)
    (hs : ∀ j, j < n → b ≤ f (a+j)) : n*b ≤ intervalSum f a n := by
  induction n with
  | zero => simp [intervalSum]
  | succ n ih =>
    simp only [intervalSum, Nat.succ_mul]
    exact Nat.add_le_add (ih (fun j hj => hs j (by omega))) (hs n (by omega))

/-- Some seed in a prescribed block has at most the specified budget
of failures, whenever the total mass across the longer interval satisfies the bound. -/
theorem exists_seed_le (f : Nat → Nat) (a n h r : Nat) (hn : 0 < n)
    (hbudget : h * intervalSum f a (n+h) ≤ n*r) :
    ∃ j < n, intervalSum f (a+j) h ≤ r := by
  apply Classical.byContradiction
  intro hnseed
  have all_bad : ∀ j, j < n → r+1 ≤ intervalSum f (a+j) h := by
    intro j hj
    apply Nat.lt_of_not_ge
    exact fun hf => hnseed ⟨j,hj,hf⟩
  have lower := constant_lower (fun t => intervalSum f t h) a n (r+1) all_bad
  have total := Nat.le_trans (sum_of_windows_le f a n h) hbudget
  rw [Nat.mul_succ] at lower
  omega

/-- For shifts A in [w,2w], the tested offsets are A+1 through A+h. -/
theorem exists_divisibility_seed (M w h r : Nat)
    (budget : h * intervalSum (fun m => if m ∣ M then 0 else 1)
      (w+1) (w+1+h) ≤ (w+1)*r) :
    ∃ A, w ≤ A ∧ A ≤ 2*w ∧
      intervalSum (fun m => if m ∣ M then 0 else 1) (A+1) h ≤ r := by
  obtain ⟨j,hj,hit⟩ := exists_seed_le _ (w+1) (w+1) h r (by omega) budget
  refine ⟨w+j, by omega, by omega, ?_⟩
  simpa only [Nat.add_right_comm w 1 j] using hit

/-- Number of listed moduli that divide m, with repetitions allowed. -/
def hits (qs : List Nat) (m : Nat) : Nat :=
  (qs.map (fun q => if q ∣ m then 1 else 0)).sum

theorem hits_pos_of_mem {qs : List Nat} {q m : Nat}
    (hq : q ∈ qs) (hd : q ∣ m) : 1 ≤ hits qs m := by
  induction qs with
  | nil => simp at hq
  | cons p qs ih =>
    rcases List.mem_cons.mp hq with rfl | h
    · simp [hits, hd]
    · have := ih h
      change 1 ≤ (if p ∣ m then 1 else 0) + hits qs m
      omega

theorem sum_multiples (q z : Nat) :
    intervalSum (fun m => if q ∣ m then 1 else 0) 1 z = z/q := by
  induction z with
  | zero => simp [intervalSum]
  | succ z ih =>
    rw [Nat.succ_div]
    simp only [intervalSum, ih, Nat.add_comm 1 z]

theorem sum_hits (qs : List Nat) (z : Nat) :
    intervalSum (hits qs) 1 z = (qs.map (fun q => z/q)).sum := by
  induction qs with
  | nil =>
    induction z with
    | zero => rfl
    | succ z ih => simpa [intervalSum, hits] using ih
  | cons q qs ih =>
    change intervalSum (fun m => (if q ∣ m then 1 else 0) + hits qs m) 1 z =
      z/q + (qs.map (fun p => z/p)).sum
    rw [intervalSum_pointwise_add, sum_multiples, ih]

theorem sum_mono (f g : Nat → Nat) (a n : Nat)
    (hfg : ∀ j, j < n → f (a+j) ≤ g (a+j)) :
    intervalSum f a n ≤ intervalSum g a n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih => exact Nat.add_le_add (ih (fun j hj => hfg j (by omega))) (hfg n (by omega))

/-- A finite union bound and averaging over seeds. Supply a list qs of
obstructions to m dividing M. The resulting budget uses the exact number
of positive multiples of each q up to the endpoint. -/
theorem exists_seed_of_obstructions (M w h r : Nat) (qs : List Nat)
    (hcovers : ∀ m, 0 < m → m ≤ 2*w+h+1 → ¬ m ∣ M → ∃ q ∈ qs, q ∣ m)
    (hbudget : h * (qs.map (fun q => (2*w+h+1)/q)).sum ≤ (w+1)*r) :
    ∃ A, w ≤ A ∧ A ≤ 2*w ∧
      intervalSum (fun m => if m ∣ M then 0 else 1) (A+1) h ≤ r := by
  apply exists_divisibility_seed
  apply Nat.le_trans _ hbudget
  apply Nat.mul_le_mul_left
  have hbound := sum_mono (fun m => if m ∣ M then 0 else 1) (hits qs) (w+1) (w+1+h) (by
    intro j hj
    by_cases hd : w+1+j ∣ M
    · simp [hd]
    · simp only [hd, if_false]
      obtain ⟨q, hq, hm⟩ := hcovers _ (by omega) (by omega) hd
      exact hits_pos_of_mem hq hm)
  have shifted := shifted_sum_le (hits qs) 1 w (w+1+h)
  rw [Nat.add_comm 1 w, show w+(w+1+h)=2*w+h+1 by omega, sum_hits] at shifted
  exact Nat.le_trans hbound shifted

end SeedAverage
