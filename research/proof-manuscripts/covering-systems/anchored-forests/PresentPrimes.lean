import PacketAssignment

/-! Codex (OpenAI). Joint deletion of the genuinely present primes 7 and 11.
The finite computation and residue periodicity pertain to the same placement.
The independent packet certificate permits complete residue reassignment. -/
namespace PresentPrimes

def stages : List (List Nat) :=
  [[2,2],[4,4],[12,3,6],[60,5,10,15,20],[420,7,14,21,28,35,42],
   [11,22,33,44,55,66,77,110,132,165,220]]
def moduli := PacketEssential.Flat 1 stages

theorem sizeAndCap : moduli.Nodup ∧ moduli.length=25 ∧ moduli.max?=some 220 := by decide

theorem all_reassignments (f : Nat → Option Int) (cover : ∀ x, PacketEssential.Outside moduli f x) :
    ∀ n ∈ moduli, f n ≠ none := PacketEssential.essential (by decide) f cover

def phases : List (Nat × Int) :=
 [(2,1),(4,2),(3,1),(6,2),(5,1),(10,2),(15,3),(20,4),
  (7,1),(14,2),(21,3),(28,4),(35,5),(42,6),
  (11,0),(22,12),(33,24),(44,36),(55,15),(66,60),(77,28),(110,40),
  (132,96),(165,75),(220,120)]

theorem sameRows : (phases.map Prod.fst).Nodup ∧ ∀ n, n ∈ phases.map Prod.fst ↔ n ∈ moduli := by
  constructor
  · decide
  · intro n
    simp [moduli, phases, stages, PacketEssential.Flat]
    grind

def old := phases.filter (fun e => e.1 % 7 != 0 && e.1 % 11 != 0)
def hit (rs : List (Nat × Int)) (x : Int) := rs.any (fun e => x % (e.1:Int) == e.2)

private theorem reduceHit (rs : List (Nat × Int)) (D : Int)
    (h : ∀ e∈rs, (e.1:Int) ∣ D) (x : Int) : hit rs (x%D) = hit rs x := by
  apply Bool.eq_iff_iff.mpr
  simp only [hit, List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨e,he,hh⟩
    exact ⟨e,he,by simpa only [Int.emod_emod_of_dvd x (h e he)] using hh⟩
  · rintro ⟨e,he,hh⟩
    exact ⟨e,he,by simpa only [Int.emod_emod_of_dvd x (h e he)] using hh⟩

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private theorem table : ∀ i : Fin 70, ∀ j : Fin 66,
    hit phases (↑(i.val*66+j.val) : Int) = true := by decide

theorem covers (x : Int) : hit phases x = true := by
  let y := (x%4620).toNat
  have non : 0≤x%4620 := Int.emod_nonneg _ (by decide)
  have bound : x%4620<4620 := Int.emod_lt_of_pos _ (by decide)
  have eq : (y:Int)=x%4620 := Int.toNat_of_nonneg non
  have under : y<4620 := by omega
  have h := table ⟨y/66,by omega⟩ ⟨y%66,by omega⟩
  have ar : y/66*66+y%66=y := by omega
  rw [← reduceHit phases 4620 (by decide) x, ←eq]
  simpa only [ar] using h

theorem jointDeletion (x : Int) : hit old x = false ↔ x%60=0 := by
  let y := (x%60).toNat
  have non : 0≤x%60 := Int.emod_nonneg _ (by decide)
  have under : x%60<60 := Int.emod_lt_of_pos _ (by decide)
  have eq : (y:Int)=x%60 := Int.toNat_of_nonneg non
  have tab : ∀ i : Fin 60, hit old (i.val:Int)=false ↔ (i.val:Int)=0 := by decide
  rw [← reduceHit old 60 (by decide) x, ←eq]
  exact tab ⟨y,by omega⟩

#print axioms all_reassignments
#print axioms covers
#print axioms jointDeletion
end PresentPrimes
