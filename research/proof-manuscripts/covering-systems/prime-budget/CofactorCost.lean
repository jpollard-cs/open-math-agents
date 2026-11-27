import Std

/-! The four-prime arithmetic check for C(11,16). If b(Q)<10 and
11 does not divide Q, only 2,3,5,7 are affordable; extra exponents
above those needed by divisors <=16 can only increase the cost. -/
namespace CofactorCost
def slots (Q : Nat) : Nat :=
  ((List.range 16).filter (fun i => Q % (i+1) == 0)).length

theorem belowTen :
    ∀ a : Fin 5, ∀ b : Fin 3, ∀ c : Fin 2, ∀ d : Fin 2,
    a.val + 2*b.val + 4*c.val + 6*d.val < 10 →
      slots (2^a.val * 3^b.val * 5^c.val * 7^d.val) < 11 := by decide

theorem attained : 11 ≤ slots 240 := by decide
#print axioms belowTen
#print axioms attained
end CofactorCost
