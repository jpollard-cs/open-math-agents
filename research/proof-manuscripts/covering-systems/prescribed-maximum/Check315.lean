import Mathlib

/-! Finite certificates for the prescribed-maximum construction.
The analytic or infinitary status of any other problem plays no role here. -/
namespace PrescribedMaximum

/-- Each of p sites in a private-point fiber needs a different class. -/
theorem fiber_count {Point Label : Type*} [DecidableEq Label]
    (fiber : Finset Point) (top : Finset Label) (owner : Point → Label)
    (hmem : ∀ x ∈ fiber, owner x ∈ top)
    (huniq : Set.InjOn owner (↑fiber : Set Point)) :
    fiber.card ≤ top.card :=
  Finset.card_le_card_of_injOn owner hmem huniq

def witness : List (Nat × Nat) :=
  [(2,1),(3,1),(5,1),(6,2),(7,0),(9,3),(10,2),(14,8),
   (15,3),(18,6),(21,9),(30,24),(35,10),(42,18),(63,54),(315,90)]

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem period_covered :
    (List.range 630).all (fun x => witness.any (fun mr => x % mr.1 == mr.2)) = true := by
  decide

theorem all_moduli_divide_period :
    witness.all (fun mr => 630 % mr.1 == 0) = true := by decide

/-- On divisors of 630 = 2 * 3^2 * 5 * 7, calculated from the exponents. -/
def cost630 (d : Nat) : Nat :=
  (if d % 2 = 0 then 1 else 0) + (if d % 3 = 0 then 2 else 0) +
  (if d % 9 = 0 then 2 else 0) + (if d % 5 = 0 then 4 else 0) +
  (if d % 7 = 0 then 6 else 0)

theorem proper_period_budget :
    (List.range 630).all (fun d =>
      d == 0 || 630 % d != 0 ||
      decide ((witness.filter (fun mr => d % mr.1 == 0)).length ≤ cost630 d)) = true := by
  decide

theorem full_period_budget : witness.length = cost630 630 + 1 := by decide

#print axioms fiber_count
#print axioms period_covered
#print axioms proper_period_budget
end PrescribedMaximum
