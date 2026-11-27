import Std

/-! The 33 rows below cover every integer after deleting 56, 63 and 80 from the sole
size-36 candidate at cap 108. The candidate exhaustion is documented separately. -/

namespace Erdos1189.Size36ProperDeletion
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows : List (Int × Int) :=
  [(5, 3), (6, 1), (7, 0), (8, 2), (9, 2),
   (10, 1), (12, 4), (14, 8), (15, 9), (16, 6),
   (18, 5), (20, 7), (21, 9), (24, 22), (27, 5),
   (28, 24), (30, 15), (32, 14), (35, 20), (36, 8),
   (40, 17), (42, 18), (45, 35), (48, 14), (54, 14),
   (60, 57), (70, 62), (72, 53), (84, 12), (90, 89),
   (96, 30), (105, 6), (108, 104)]

private theorem block_0 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((0 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_1 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((30 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_2 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((60 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_3 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((90 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_4 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((120 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_5 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((150 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_6 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((180 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_7 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((210 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_8 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((240 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_9 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((270 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_10 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((300 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_11 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((330 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_12 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((360 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem block_13 :
    ∀ a : Fin 30, ∀ b : Fin 72,
      rows.any (fun s => (((390 + a.val) * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem finite_cover :
    ∀ a : Fin 420, ∀ b : Fin 72,
      rows.any (fun s => ((a.val * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by
  intro a b
  by_cases h0 : a.val < 30
  · let q : Fin 30 := ⟨a.val - 0, by omega⟩
    have hq : 0 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_0 q b
  by_cases h1 : a.val < 60
  · let q : Fin 30 := ⟨a.val - 30, by omega⟩
    have hq : 30 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_1 q b
  by_cases h2 : a.val < 90
  · let q : Fin 30 := ⟨a.val - 60, by omega⟩
    have hq : 60 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_2 q b
  by_cases h3 : a.val < 120
  · let q : Fin 30 := ⟨a.val - 90, by omega⟩
    have hq : 90 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_3 q b
  by_cases h4 : a.val < 150
  · let q : Fin 30 := ⟨a.val - 120, by omega⟩
    have hq : 120 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_4 q b
  by_cases h5 : a.val < 180
  · let q : Fin 30 := ⟨a.val - 150, by omega⟩
    have hq : 150 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_5 q b
  by_cases h6 : a.val < 210
  · let q : Fin 30 := ⟨a.val - 180, by omega⟩
    have hq : 180 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_6 q b
  by_cases h7 : a.val < 240
  · let q : Fin 30 := ⟨a.val - 210, by omega⟩
    have hq : 210 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_7 q b
  by_cases h8 : a.val < 270
  · let q : Fin 30 := ⟨a.val - 240, by omega⟩
    have hq : 240 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_8 q b
  by_cases h9 : a.val < 300
  · let q : Fin 30 := ⟨a.val - 270, by omega⟩
    have hq : 270 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_9 q b
  by_cases h10 : a.val < 330
  · let q : Fin 30 := ⟨a.val - 300, by omega⟩
    have hq : 300 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_10 q b
  by_cases h11 : a.val < 360
  · let q : Fin 30 := ⟨a.val - 330, by omega⟩
    have hq : 330 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_11 q b
  by_cases h12 : a.val < 390
  · let q : Fin 30 := ⟨a.val - 360, by omega⟩
    have hq : 360 + q.val = a.val := by dsimp [q]; omega
    simpa only [hq] using block_12 q b
  let q : Fin 30 := ⟨a.val - 390, by omega⟩
  have hq : 390 + q.val = a.val := by dsimp [q]; omega
  simpa only [hq] using block_13 q b

private theorem period_multiples :
    rows.all (fun s => (30240 : Int) % s.1 == 0) = true := by decide

theorem covers (n : Int) : ∃ s ∈ rows, n % s.1 = s.2 := by
  have hn := Int.emod_nonneg n (by decide : (30240 : Int) ≠ 0)
  have hl := Int.emod_lt_of_pos n (by decide : (0 : Int) < 30240)
  let t := (n % 30240).toNat
  have ht : t < 30240 := (Int.toNat_lt hn).mpr hl
  let a : Fin 420 := ⟨t / 72, by omega⟩
  let b : Fin 72 := ⟨t % 72, Nat.mod_lt _ (by decide)⟩
  have hab : a.val * 72 + b.val = t := by dsimp [a,b]; omega
  obtain ⟨s, hs, he⟩ := List.any_eq_true.mp (finite_cover a b)
  have hit : ((a.val * 72 + b.val : Nat) : Int) % s.1 = s.2 := by simpa using he
  rw [hab] at hit
  have hcast : (t : Int) = n % 30240 := Int.toNat_of_nonneg hn
  have hdiv : s.1 ∣ (30240 : Int) := by
    apply Int.dvd_of_emod_eq_zero
    simpa using (List.all_eq_true.mp period_multiples s hs)
  rw [hcast, Int.emod_emod_of_dvd n hdiv] at hit
  exact ⟨s, hs, hit⟩

theorem size_and_max :
    rows.length = 33 ∧ (rows.map Prod.fst).Nodup ∧
    (rows.map Prod.fst).max? = some 108 := by decide

#print axioms covers
#print axioms size_and_max
end Erdos1189.Size36ProperDeletion
