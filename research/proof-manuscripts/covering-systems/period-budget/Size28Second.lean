import Std

/-! Covering witness at the 28-modulus upper bound for Erdős problem 1189.
The proofs below establish coverage for all integers and the size, distinctness,
and maximum of the list. Irreducibility is checked by separate exhaustive solvers. -/

namespace Erdos1189.Size28Second
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def rows : List (Int × Int) :=
  [(3, 1), (5, 1), (6, 2), (7, 0), (9, 0),
   (10, 3), (14, 1), (15, 2), (16, 7), (18, 12),
   (20, 9), (21, 9), (24, 6), (28, 3), (30, 5),
   (35, 25), (36, 24), (40, 19), (42, 33), (45, 15),
   (48, 15), (56, 27), (60, 57), (63, 3), (70, 67),
   (72, 42), (80, 79), (84, 69)]

private theorem finite_cover :
    ∀ a : Fin 70, ∀ b : Fin 72,
      rows.any (fun s => ((a.val * 72 + b.val : Nat) : Int) % s.1 == s.2) = true := by decide

private theorem period_multiples :
    rows.all (fun s => (5040 : Int) % s.1 == 0) = true := by decide

theorem covers (n : Int) : ∃ s ∈ rows, n % s.1 = s.2 := by
  have hn := Int.emod_nonneg n (by decide : (5040 : Int) ≠ 0)
  have hl := Int.emod_lt_of_pos n (by decide : (0 : Int) < 5040)
  let t := (n % 5040).toNat
  have ht : t < 5040 := (Int.toNat_lt hn).mpr hl
  let a : Fin 70 := ⟨t / 72, by omega⟩
  let b : Fin 72 := ⟨t % 72, Nat.mod_lt _ (by decide)⟩
  have hab : a.val * 72 + b.val = t := by dsimp [a,b]; omega
  obtain ⟨s, hs, he⟩ := List.any_eq_true.mp (finite_cover a b)
  have hit : ((a.val * 72 + b.val : Nat) : Int) % s.1 = s.2 := by simpa using he
  rw [hab] at hit
  have hcast : (t : Int) = n % 5040 := Int.toNat_of_nonneg hn
  have hdiv : s.1 ∣ (5040 : Int) := by
    apply Int.dvd_of_emod_eq_zero
    simpa using (List.all_eq_true.mp period_multiples s hs)
  rw [hcast, Int.emod_emod_of_dvd n hdiv] at hit
  exact ⟨s, hs, hit⟩

theorem size_and_max :
    rows.length = 28 ∧ (rows.map Prod.fst).Nodup ∧
    (rows.map Prod.fst).max? = some 84 := by decide

#print axioms covers
#print axioms size_and_max
end Erdos1189.Size28Second
