import PacketAssignment

/-! AI-authored certificate for the doubled-period minimum-cardinality witness at 462. -/
namespace Even462
open PacketEssential

def stages : List (List Nat) :=
  [[2,2],[4,4],[12,3,12],[84,7,14,21,28,42,84],
   [462,11,22,33,44,66,77,132,154,231,308]]

def moduli := Flat 1 stages

theorem sizeAndCap : moduli.Nodup ∧ moduli.length = 21 ∧ moduli.max? = some 462 := by decide

theorem integerCover : ∃ a : Nat → Int, ∀ x : Int, ∃ n ∈ moduli, (n : Int) ∣ x - a n :=
  PacketAssignment.covers (stages := stages) (by decide) sizeAndCap.1

theorem every_reassignment (f : Nat → Option Int) (h : ∀ x, Outside moduli f x) :
    ∀ n ∈ moduli, f n ≠ none :=
  PacketEssential.essential (stages := stages) (by decide) f h

#print axioms integerCover
#print axioms every_reassignment
end Even462
