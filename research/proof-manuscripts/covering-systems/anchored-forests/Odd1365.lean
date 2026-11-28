import PacketAssignment
/-! An AI-authored all-integers and arbitrary-reassignment certificate. -/
namespace Odd1365
open PacketEssential

def stages : List (List Nat) :=
  [[2, 2], [6, 3, 6], [30, 5, 10, 15, 30], [210, 7, 14, 21, 35, 42, 70], [1365, 13, 26, 39, 65, 78, 91, 130, 182, 195, 273, 390, 455]]

def moduli := Flat 1 stages

theorem sizeAndCap : moduli.Nodup ∧ moduli.length = 26 ∧ moduli.max? = some 1365 := by decide

theorem integerCover : ∃ a : Nat → Int, ∀ x : Int, ∃ n ∈ moduli, (n : Int) ∣ x - a n :=
  PacketAssignment.covers (stages := stages) (by decide) sizeAndCap.1

theorem every_reassignment (f : Nat → Option Int) (h : ∀ x, Outside moduli f x) :
    ∀ n ∈ moduli, f n ≠ none :=
  PacketEssential.essential (stages := stages) (by decide) f h

#print axioms integerCover
#print axioms every_reassignment
end Odd1365
