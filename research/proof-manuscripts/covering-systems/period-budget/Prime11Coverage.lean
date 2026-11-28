import Std

/-! Coverage certificates for ten distinct cardinalities in Erdős problem 1189.
The common eleven rows cover every multiple of 2520. Each ordinary list
covers every other integer. The written irreducibility and lower-bound
arguments use the cited earlier finite census. -/

namespace Erdos1189.Prime11
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev Rows := List (Int × Int)
def Covers (rows : Rows) (n : Int) := ∃ s ∈ rows, n % s.1 = s.2

private theorem liftHit (rows : Rows) (n P : Int)
    (divs : rows.all (fun s => P % s.1 == 0) = true)
    (hit : rows.any (fun s => (n % P) % s.1 == s.2) = true) :
    Covers rows n := by
  obtain ⟨s, hs, he⟩ := List.any_eq_true.mp hit
  have hd : s.1 ∣ P := Int.dvd_of_emod_eq_zero (by simpa using List.all_eq_true.mp divs s hs)
  exact ⟨s, hs, by simpa [Int.emod_emod_of_dvd n hd] using he⟩

def branches : Rows :=
  [(11, 0), (22, 12), (33, 24), (44, 36), (55, 15),
   (66, 60), (77, 28), (88, 40), (99, 63), (110, 20),
   (132, 120)]

private theorem branchTable : ∀ a : Fin 11,
    branches.any (fun s => (2520 * (a.val : Int)) % s.1 == s.2) = true := by decide

private theorem branchCover (n : Int) (hz : n % 2520 = 0) : Covers branches n := by
  have hn := Int.emod_nonneg n (by decide : (27720 : Int) ≠ 0)
  have hl := Int.emod_lt_of_pos n (by decide : (0 : Int) < 27720)
  have hz' : (n % 27720) % 2520 = 0 := by
    rw [Int.emod_emod_of_dvd n (by decide : (2520 : Int) ∣ 27720), hz]
  let t := (n % 27720).toNat
  have hcast : (t : Int) = n % 27720 := Int.toNat_of_nonneg hn
  let a : Fin 11 := ⟨t / 2520, by omega⟩
  have hv : 2520 * (a.val : Int) = n % 27720 := by dsimp [a]; omega
  apply liftHit branches n 27720 (by decide)
  rw [← hv]
  exact branchTable a

private theorem extend (ordinary : Rows) (n : Int)
    (h : Covers ((2520,0) :: ordinary) n) : Covers (ordinary ++ branches) n := by
  obtain ⟨s, hs, he⟩ := h
  rcases List.mem_cons.mp hs with e | mem
  · subst s
    obtain ⟨b, hb, eqn⟩ := branchCover n he
    exact ⟨b, List.mem_append_right _ hb, eqn⟩
  · exact ⟨s, List.mem_append_left _ mem, he⟩

private theorem fromTable (ordinary : Rows) (blocks : Nat) (positive : 0 < blocks)
    (divs : ((2520,0) :: ordinary).all (fun s => ((blocks * 720 : Nat) : Int) % s.1 == 0) = true)
    (table : ∀ i : Fin blocks, ∀ j : Fin 10, ∀ t : Fin 72,
      ((2520,0) :: ordinary).any (fun s =>
        ((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2) = true)
    (n : Int) : Covers (ordinary ++ branches) n := by
  apply extend
  let P : Int := (blocks * 720 : Nat)
  have hp : 0 < P := by dsimp [P]; omega
  have hn := Int.emod_nonneg n (by omega : P ≠ 0)
  have hl := Int.emod_lt_of_pos n hp
  let v := (n % P).toNat
  have hv : (v : Int) = n % P := Int.toNat_of_nonneg hn
  have bound : v < blocks * 720 := (Int.toNat_lt hn).mpr hl
  let i : Fin blocks := ⟨v / 720, by omega⟩
  let j : Fin 10 := ⟨(v % 720) / 72, by omega⟩
  let t : Fin 72 := ⟨v % 72, by omega⟩
  have recombine : i.val * 720 + j.val * 72 + t.val = v := by dsimp [i,j,t]; omega
  apply liftHit _ n P divs
  have h := table i j t
  simpa only [recombine, hv] using h

namespace Size34

def ordinary : Rows :=
  [(3, 1), (5, 1), (6, 3), (9, 3), (10, 2),
   (12, 5), (14, 8), (15, 5), (16, 7), (18, 6),
   (20, 4), (21, 9), (24, 11), (28, 24), (30, 8),
   (35, 25), (36, 18), (40, 20), (42, 12), (45, 18),
   (48, 47), (56, 48), (60, 14)]

private theorem block0 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((0 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block1 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((1 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block2 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((2 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block3 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((3 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block4 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((4 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block5 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((5 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block6 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((6 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide

private theorem table (i : Fin 7) : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by
  by_cases e0 : i.val = 0
  · simpa only [e0] using block0
  by_cases e1 : i.val = 1
  · simpa only [e1] using block1
  by_cases e2 : i.val = 2
  · simpa only [e2] using block2
  by_cases e3 : i.val = 3
  · simpa only [e3] using block3
  by_cases e4 : i.val = 4
  · simpa only [e4] using block4
  by_cases e5 : i.val = 5
  · simpa only [e5] using block5
  have last : i.val = 6 := by omega
  simpa only [last] using block6

theorem covers (n : Int) : Covers (ordinary ++ branches) n :=
  fromTable ordinary 7 (by decide) (by decide) table n

theorem size_and_max :
    (ordinary ++ branches).length = 34 ∧
    ((ordinary ++ branches).map Prod.fst).Nodup ∧
    ((ordinary ++ branches).map Prod.fst).max? = some 132 := by decide

#print axioms covers
#print axioms size_and_max
end Size34

namespace Size35

def ordinary : Rows :=
  [(4, 1), (5, 1), (6, 2), (8, 3), (9, 3),
   (10, 2), (12, 3), (14, 8), (15, 10), (16, 7),
   (18, 6), (20, 4), (21, 9), (24, 23), (28, 24),
   (30, 28), (35, 25), (36, 18), (40, 20), (42, 12),
   (45, 18), (48, 31), (56, 48), (60, 34)]

private theorem block0 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((0 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block1 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((1 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block2 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((2 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block3 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((3 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block4 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((4 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block5 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((5 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block6 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((6 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide

private theorem table (i : Fin 7) : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by
  by_cases e0 : i.val = 0
  · simpa only [e0] using block0
  by_cases e1 : i.val = 1
  · simpa only [e1] using block1
  by_cases e2 : i.val = 2
  · simpa only [e2] using block2
  by_cases e3 : i.val = 3
  · simpa only [e3] using block3
  by_cases e4 : i.val = 4
  · simpa only [e4] using block4
  by_cases e5 : i.val = 5
  · simpa only [e5] using block5
  have last : i.val = 6 := by omega
  simpa only [last] using block6

theorem covers (n : Int) : Covers (ordinary ++ branches) n :=
  fromTable ordinary 7 (by decide) (by decide) table n

theorem size_and_max :
    (ordinary ++ branches).length = 35 ∧
    ((ordinary ++ branches).map Prod.fst).Nodup ∧
    ((ordinary ++ branches).map Prod.fst).max? = some 132 := by decide

#print axioms covers
#print axioms size_and_max
end Size35

namespace Size36

def ordinary : Rows :=
  [(4, 3), (5, 4), (6, 2), (7, 4), (8, 1),
   (9, 3), (10, 2), (12, 9), (14, 12), (15, 10),
   (16, 5), (18, 6), (20, 16), (21, 6), (24, 5),
   (28, 14), (30, 28), (35, 15), (42, 30), (45, 18),
   (48, 13), (56, 28), (60, 46), (63, 45), (70, 36)]

private theorem block0 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((0 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block1 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((1 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block2 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((2 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block3 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((3 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block4 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((4 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block5 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((5 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block6 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((6 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide

private theorem table (i : Fin 7) : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by
  by_cases e0 : i.val = 0
  · simpa only [e0] using block0
  by_cases e1 : i.val = 1
  · simpa only [e1] using block1
  by_cases e2 : i.val = 2
  · simpa only [e2] using block2
  by_cases e3 : i.val = 3
  · simpa only [e3] using block3
  by_cases e4 : i.val = 4
  · simpa only [e4] using block4
  by_cases e5 : i.val = 5
  · simpa only [e5] using block5
  have last : i.val = 6 := by omega
  simpa only [last] using block6

theorem covers (n : Int) : Covers (ordinary ++ branches) n :=
  fromTable ordinary 7 (by decide) (by decide) table n

theorem size_and_max :
    (ordinary ++ branches).length = 36 ∧
    ((ordinary ++ branches).map Prod.fst).Nodup ∧
    ((ordinary ++ branches).map Prod.fst).max? = some 132 := by decide

#print axioms covers
#print axioms size_and_max
end Size36

namespace Size37

def ordinary : Rows :=
  [(4, 1), (5, 4), (6, 2), (7, 4), (8, 3),
   (9, 3), (10, 2), (12, 7), (14, 12), (15, 10),
   (16, 15), (18, 6), (20, 16), (21, 6), (28, 14),
   (30, 28), (35, 15), (36, 15), (42, 30), (45, 18),
   (48, 23), (56, 28), (60, 46), (63, 45), (70, 36),
   (72, 63)]

private theorem block0 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((0 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block1 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((1 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block2 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((2 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block3 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((3 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block4 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((4 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block5 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((5 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block6 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((6 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide

private theorem table (i : Fin 7) : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by
  by_cases e0 : i.val = 0
  · simpa only [e0] using block0
  by_cases e1 : i.val = 1
  · simpa only [e1] using block1
  by_cases e2 : i.val = 2
  · simpa only [e2] using block2
  by_cases e3 : i.val = 3
  · simpa only [e3] using block3
  by_cases e4 : i.val = 4
  · simpa only [e4] using block4
  by_cases e5 : i.val = 5
  · simpa only [e5] using block5
  have last : i.val = 6 := by omega
  simpa only [last] using block6

theorem covers (n : Int) : Covers (ordinary ++ branches) n :=
  fromTable ordinary 7 (by decide) (by decide) table n

theorem size_and_max :
    (ordinary ++ branches).length = 37 ∧
    ((ordinary ++ branches).map Prod.fst).Nodup ∧
    ((ordinary ++ branches).map Prod.fst).max? = some 132 := by decide

#print axioms covers
#print axioms size_and_max
end Size37

namespace Size38

def ordinary : Rows :=
  [(3, 1), (5, 4), (6, 5), (7, 4), (9, 3),
   (10, 6), (14, 12), (15, 5), (16, 4), (18, 15),
   (20, 2), (21, 6), (24, 3), (30, 8), (35, 8),
   (36, 9), (40, 32), (42, 30), (45, 18), (48, 12),
   (56, 24), (60, 30), (63, 42), (70, 50), (72, 63),
   (80, 12), (84, 66)]

private theorem block0 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((0 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block1 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((1 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block2 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((2 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block3 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((3 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block4 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((4 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block5 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((5 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block6 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((6 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide

private theorem table (i : Fin 7) : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by
  by_cases e0 : i.val = 0
  · simpa only [e0] using block0
  by_cases e1 : i.val = 1
  · simpa only [e1] using block1
  by_cases e2 : i.val = 2
  · simpa only [e2] using block2
  by_cases e3 : i.val = 3
  · simpa only [e3] using block3
  by_cases e4 : i.val = 4
  · simpa only [e4] using block4
  by_cases e5 : i.val = 5
  · simpa only [e5] using block5
  have last : i.val = 6 := by omega
  simpa only [last] using block6

theorem covers (n : Int) : Covers (ordinary ++ branches) n :=
  fromTable ordinary 7 (by decide) (by decide) table n

theorem size_and_max :
    (ordinary ++ branches).length = 38 ∧
    ((ordinary ++ branches).map Prod.fst).Nodup ∧
    ((ordinary ++ branches).map Prod.fst).max? = some 132 := by decide

#print axioms covers
#print axioms size_and_max
end Size38

namespace Size39

def ordinary : Rows :=
  [(3, 1), (5, 4), (7, 4), (8, 3), (9, 3),
   (10, 6), (12, 5), (14, 12), (15, 5), (16, 4),
   (18, 15), (20, 2), (21, 6), (24, 23), (30, 8),
   (35, 8), (36, 9), (40, 32), (42, 30), (45, 18),
   (48, 12), (56, 24), (60, 30), (63, 42), (70, 50),
   (72, 63), (80, 12), (84, 66)]

private theorem block0 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((0 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block1 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((1 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block2 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((2 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block3 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((3 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block4 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((4 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block5 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((5 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block6 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((6 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide

private theorem table (i : Fin 7) : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by
  by_cases e0 : i.val = 0
  · simpa only [e0] using block0
  by_cases e1 : i.val = 1
  · simpa only [e1] using block1
  by_cases e2 : i.val = 2
  · simpa only [e2] using block2
  by_cases e3 : i.val = 3
  · simpa only [e3] using block3
  by_cases e4 : i.val = 4
  · simpa only [e4] using block4
  by_cases e5 : i.val = 5
  · simpa only [e5] using block5
  have last : i.val = 6 := by omega
  simpa only [last] using block6

theorem covers (n : Int) : Covers (ordinary ++ branches) n :=
  fromTable ordinary 7 (by decide) (by decide) table n

theorem size_and_max :
    (ordinary ++ branches).length = 39 ∧
    ((ordinary ++ branches).map Prod.fst).Nodup ∧
    ((ordinary ++ branches).map Prod.fst).max? = some 132 := by decide

#print axioms covers
#print axioms size_and_max
end Size39

namespace Size40

def ordinary : Rows :=
  [(3, 1), (5, 4), (7, 4), (8, 3), (9, 3),
   (10, 6), (12, 5), (14, 12), (15, 5), (16, 4),
   (18, 15), (20, 2), (21, 6), (24, 23), (30, 8),
   (32, 12), (35, 8), (36, 9), (40, 32), (42, 30),
   (45, 18), (56, 24), (60, 30), (63, 42), (70, 50),
   (72, 63), (80, 12), (84, 66), (96, 60)]

private theorem block0 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((0 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block1 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((1 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block2 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((2 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block3 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((3 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block4 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((4 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block5 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((5 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block6 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((6 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block7 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((7 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block8 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((8 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block9 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((9 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block10 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((10 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block11 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((11 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block12 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((12 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block13 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((13 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide

private theorem table (i : Fin 14) : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by
  by_cases e0 : i.val = 0
  · simpa only [e0] using block0
  by_cases e1 : i.val = 1
  · simpa only [e1] using block1
  by_cases e2 : i.val = 2
  · simpa only [e2] using block2
  by_cases e3 : i.val = 3
  · simpa only [e3] using block3
  by_cases e4 : i.val = 4
  · simpa only [e4] using block4
  by_cases e5 : i.val = 5
  · simpa only [e5] using block5
  by_cases e6 : i.val = 6
  · simpa only [e6] using block6
  by_cases e7 : i.val = 7
  · simpa only [e7] using block7
  by_cases e8 : i.val = 8
  · simpa only [e8] using block8
  by_cases e9 : i.val = 9
  · simpa only [e9] using block9
  by_cases e10 : i.val = 10
  · simpa only [e10] using block10
  by_cases e11 : i.val = 11
  · simpa only [e11] using block11
  by_cases e12 : i.val = 12
  · simpa only [e12] using block12
  have last : i.val = 13 := by omega
  simpa only [last] using block13

theorem covers (n : Int) : Covers (ordinary ++ branches) n :=
  fromTable ordinary 14 (by decide) (by decide) table n

theorem size_and_max :
    (ordinary ++ branches).length = 40 ∧
    ((ordinary ++ branches).map Prod.fst).Nodup ∧
    ((ordinary ++ branches).map Prod.fst).max? = some 132 := by decide

#print axioms covers
#print axioms size_and_max
end Size40

namespace Size41

def ordinary : Rows :=
  [(3, 1), (5, 4), (7, 4), (8, 3), (9, 3),
   (10, 6), (12, 5), (14, 12), (15, 5), (16, 4),
   (18, 15), (20, 2), (21, 6), (24, 23), (27, 9),
   (30, 8), (35, 8), (40, 32), (42, 30), (45, 18),
   (48, 12), (54, 45), (56, 24), (60, 30), (63, 42),
   (70, 50), (72, 63), (80, 12), (84, 66), (108, 81)]

private theorem block0 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((0 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block1 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((1 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block2 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((2 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block3 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((3 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block4 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((4 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block5 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((5 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block6 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((6 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block7 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((7 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block8 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((8 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block9 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((9 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block10 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((10 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block11 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((11 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block12 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((12 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block13 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((13 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block14 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((14 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block15 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((15 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block16 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((16 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block17 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((17 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block18 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((18 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block19 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((19 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block20 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((20 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide

private theorem table (i : Fin 21) : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by
  by_cases e0 : i.val = 0
  · simpa only [e0] using block0
  by_cases e1 : i.val = 1
  · simpa only [e1] using block1
  by_cases e2 : i.val = 2
  · simpa only [e2] using block2
  by_cases e3 : i.val = 3
  · simpa only [e3] using block3
  by_cases e4 : i.val = 4
  · simpa only [e4] using block4
  by_cases e5 : i.val = 5
  · simpa only [e5] using block5
  by_cases e6 : i.val = 6
  · simpa only [e6] using block6
  by_cases e7 : i.val = 7
  · simpa only [e7] using block7
  by_cases e8 : i.val = 8
  · simpa only [e8] using block8
  by_cases e9 : i.val = 9
  · simpa only [e9] using block9
  by_cases e10 : i.val = 10
  · simpa only [e10] using block10
  by_cases e11 : i.val = 11
  · simpa only [e11] using block11
  by_cases e12 : i.val = 12
  · simpa only [e12] using block12
  by_cases e13 : i.val = 13
  · simpa only [e13] using block13
  by_cases e14 : i.val = 14
  · simpa only [e14] using block14
  by_cases e15 : i.val = 15
  · simpa only [e15] using block15
  by_cases e16 : i.val = 16
  · simpa only [e16] using block16
  by_cases e17 : i.val = 17
  · simpa only [e17] using block17
  by_cases e18 : i.val = 18
  · simpa only [e18] using block18
  by_cases e19 : i.val = 19
  · simpa only [e19] using block19
  have last : i.val = 20 := by omega
  simpa only [last] using block20

theorem covers (n : Int) : Covers (ordinary ++ branches) n :=
  fromTable ordinary 21 (by decide) (by decide) table n

theorem size_and_max :
    (ordinary ++ branches).length = 41 ∧
    ((ordinary ++ branches).map Prod.fst).Nodup ∧
    ((ordinary ++ branches).map Prod.fst).max? = some 132 := by decide

#print axioms covers
#print axioms size_and_max
end Size41

namespace Size42

def ordinary : Rows :=
  [(3, 1), (5, 4), (7, 4), (8, 3), (9, 3),
   (10, 6), (12, 5), (14, 12), (15, 5), (16, 4),
   (18, 15), (20, 2), (21, 6), (24, 23), (27, 9),
   (30, 8), (32, 12), (35, 8), (40, 32), (42, 30),
   (45, 18), (54, 45), (56, 24), (60, 30), (63, 42),
   (70, 50), (72, 63), (80, 12), (84, 66), (96, 60),
   (108, 81)]

private theorem block0 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((0 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block1 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((1 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block2 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((2 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block3 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((3 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block4 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((4 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block5 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((5 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block6 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((6 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block7 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((7 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block8 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((8 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block9 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((9 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block10 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((10 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block11 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((11 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block12 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((12 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block13 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((13 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block14 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((14 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block15 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((15 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block16 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((16 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block17 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((17 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block18 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((18 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block19 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((19 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block20 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((20 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block21 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((21 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block22 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((22 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block23 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((23 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block24 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((24 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block25 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((25 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block26 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((26 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block27 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((27 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block28 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((28 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block29 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((29 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block30 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((30 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block31 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((31 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block32 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((32 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block33 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((33 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block34 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((34 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block35 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((35 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block36 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((36 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block37 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((37 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block38 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((38 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block39 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((39 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block40 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((40 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block41 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((41 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide

private theorem table (i : Fin 42) : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by
  by_cases e0 : i.val = 0
  · simpa only [e0] using block0
  by_cases e1 : i.val = 1
  · simpa only [e1] using block1
  by_cases e2 : i.val = 2
  · simpa only [e2] using block2
  by_cases e3 : i.val = 3
  · simpa only [e3] using block3
  by_cases e4 : i.val = 4
  · simpa only [e4] using block4
  by_cases e5 : i.val = 5
  · simpa only [e5] using block5
  by_cases e6 : i.val = 6
  · simpa only [e6] using block6
  by_cases e7 : i.val = 7
  · simpa only [e7] using block7
  by_cases e8 : i.val = 8
  · simpa only [e8] using block8
  by_cases e9 : i.val = 9
  · simpa only [e9] using block9
  by_cases e10 : i.val = 10
  · simpa only [e10] using block10
  by_cases e11 : i.val = 11
  · simpa only [e11] using block11
  by_cases e12 : i.val = 12
  · simpa only [e12] using block12
  by_cases e13 : i.val = 13
  · simpa only [e13] using block13
  by_cases e14 : i.val = 14
  · simpa only [e14] using block14
  by_cases e15 : i.val = 15
  · simpa only [e15] using block15
  by_cases e16 : i.val = 16
  · simpa only [e16] using block16
  by_cases e17 : i.val = 17
  · simpa only [e17] using block17
  by_cases e18 : i.val = 18
  · simpa only [e18] using block18
  by_cases e19 : i.val = 19
  · simpa only [e19] using block19
  by_cases e20 : i.val = 20
  · simpa only [e20] using block20
  by_cases e21 : i.val = 21
  · simpa only [e21] using block21
  by_cases e22 : i.val = 22
  · simpa only [e22] using block22
  by_cases e23 : i.val = 23
  · simpa only [e23] using block23
  by_cases e24 : i.val = 24
  · simpa only [e24] using block24
  by_cases e25 : i.val = 25
  · simpa only [e25] using block25
  by_cases e26 : i.val = 26
  · simpa only [e26] using block26
  by_cases e27 : i.val = 27
  · simpa only [e27] using block27
  by_cases e28 : i.val = 28
  · simpa only [e28] using block28
  by_cases e29 : i.val = 29
  · simpa only [e29] using block29
  by_cases e30 : i.val = 30
  · simpa only [e30] using block30
  by_cases e31 : i.val = 31
  · simpa only [e31] using block31
  by_cases e32 : i.val = 32
  · simpa only [e32] using block32
  by_cases e33 : i.val = 33
  · simpa only [e33] using block33
  by_cases e34 : i.val = 34
  · simpa only [e34] using block34
  by_cases e35 : i.val = 35
  · simpa only [e35] using block35
  by_cases e36 : i.val = 36
  · simpa only [e36] using block36
  by_cases e37 : i.val = 37
  · simpa only [e37] using block37
  by_cases e38 : i.val = 38
  · simpa only [e38] using block38
  by_cases e39 : i.val = 39
  · simpa only [e39] using block39
  by_cases e40 : i.val = 40
  · simpa only [e40] using block40
  have last : i.val = 41 := by omega
  simpa only [last] using block41

theorem covers (n : Int) : Covers (ordinary ++ branches) n :=
  fromTable ordinary 42 (by decide) (by decide) table n

theorem size_and_max :
    (ordinary ++ branches).length = 42 ∧
    ((ordinary ++ branches).map Prod.fst).Nodup ∧
    ((ordinary ++ branches).map Prod.fst).max? = some 132 := by decide

#print axioms covers
#print axioms size_and_max
end Size42

namespace Size43

def ordinary : Rows :=
  [(4, 1), (5, 3), (6, 2), (7, 3), (10, 7),
   (12, 4), (14, 4), (15, 9), (16, 3), (18, 12),
   (20, 11), (21, 12), (24, 22), (27, 6), (28, 14),
   (30, 19), (32, 26), (40, 15), (42, 36), (45, 36),
   (48, 34), (54, 42), (56, 48), (60, 59), (63, 51),
   (70, 30), (72, 36), (80, 75), (84, 6), (90, 72),
   (96, 10), (108, 24)]

private theorem block0 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((0 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block1 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((1 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block2 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((2 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block3 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((3 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block4 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((4 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block5 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((5 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block6 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((6 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block7 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((7 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block8 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((8 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block9 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((9 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block10 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((10 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block11 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((11 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block12 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((12 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block13 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((13 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block14 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((14 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block15 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((15 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block16 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((16 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block17 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((17 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block18 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((18 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block19 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((19 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block20 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((20 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block21 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((21 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block22 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((22 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block23 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((23 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block24 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((24 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block25 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((25 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block26 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((26 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block27 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((27 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block28 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((28 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block29 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((29 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block30 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((30 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block31 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((31 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block32 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((32 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block33 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((33 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block34 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((34 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block35 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((35 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block36 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((36 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block37 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((37 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block38 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((38 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block39 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((39 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block40 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((40 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide
private theorem block41 : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((41 * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by decide

private theorem table (i : Fin 42) : ∀ j : Fin 10, ∀ t : Fin 72,
    ((2520,0) :: ordinary).any (fun s => (((i.val * 720 + j.val * 72 + t.val : Nat) : Int) % s.1 == s.2)) = true := by
  by_cases e0 : i.val = 0
  · simpa only [e0] using block0
  by_cases e1 : i.val = 1
  · simpa only [e1] using block1
  by_cases e2 : i.val = 2
  · simpa only [e2] using block2
  by_cases e3 : i.val = 3
  · simpa only [e3] using block3
  by_cases e4 : i.val = 4
  · simpa only [e4] using block4
  by_cases e5 : i.val = 5
  · simpa only [e5] using block5
  by_cases e6 : i.val = 6
  · simpa only [e6] using block6
  by_cases e7 : i.val = 7
  · simpa only [e7] using block7
  by_cases e8 : i.val = 8
  · simpa only [e8] using block8
  by_cases e9 : i.val = 9
  · simpa only [e9] using block9
  by_cases e10 : i.val = 10
  · simpa only [e10] using block10
  by_cases e11 : i.val = 11
  · simpa only [e11] using block11
  by_cases e12 : i.val = 12
  · simpa only [e12] using block12
  by_cases e13 : i.val = 13
  · simpa only [e13] using block13
  by_cases e14 : i.val = 14
  · simpa only [e14] using block14
  by_cases e15 : i.val = 15
  · simpa only [e15] using block15
  by_cases e16 : i.val = 16
  · simpa only [e16] using block16
  by_cases e17 : i.val = 17
  · simpa only [e17] using block17
  by_cases e18 : i.val = 18
  · simpa only [e18] using block18
  by_cases e19 : i.val = 19
  · simpa only [e19] using block19
  by_cases e20 : i.val = 20
  · simpa only [e20] using block20
  by_cases e21 : i.val = 21
  · simpa only [e21] using block21
  by_cases e22 : i.val = 22
  · simpa only [e22] using block22
  by_cases e23 : i.val = 23
  · simpa only [e23] using block23
  by_cases e24 : i.val = 24
  · simpa only [e24] using block24
  by_cases e25 : i.val = 25
  · simpa only [e25] using block25
  by_cases e26 : i.val = 26
  · simpa only [e26] using block26
  by_cases e27 : i.val = 27
  · simpa only [e27] using block27
  by_cases e28 : i.val = 28
  · simpa only [e28] using block28
  by_cases e29 : i.val = 29
  · simpa only [e29] using block29
  by_cases e30 : i.val = 30
  · simpa only [e30] using block30
  by_cases e31 : i.val = 31
  · simpa only [e31] using block31
  by_cases e32 : i.val = 32
  · simpa only [e32] using block32
  by_cases e33 : i.val = 33
  · simpa only [e33] using block33
  by_cases e34 : i.val = 34
  · simpa only [e34] using block34
  by_cases e35 : i.val = 35
  · simpa only [e35] using block35
  by_cases e36 : i.val = 36
  · simpa only [e36] using block36
  by_cases e37 : i.val = 37
  · simpa only [e37] using block37
  by_cases e38 : i.val = 38
  · simpa only [e38] using block38
  by_cases e39 : i.val = 39
  · simpa only [e39] using block39
  by_cases e40 : i.val = 40
  · simpa only [e40] using block40
  have last : i.val = 41 := by omega
  simpa only [last] using block41

theorem covers (n : Int) : Covers (ordinary ++ branches) n :=
  fromTable ordinary 42 (by decide) (by decide) table n

theorem size_and_max :
    (ordinary ++ branches).length = 43 ∧
    ((ordinary ++ branches).map Prod.fst).Nodup ∧
    ((ordinary ++ branches).map Prod.fst).max? = some 132 := by decide

#print axioms covers
#print axioms size_and_max
end Size43

end Erdos1189.Prime11
