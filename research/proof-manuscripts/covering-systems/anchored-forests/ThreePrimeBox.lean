import Std

/-! Exact integral three-dimensional line budgets, under free placement of every line.
    Codex (OpenAI), November 2026. -/
namespace ThreePrimeBox

abbrev Cell (a b c : Nat) := Fin a × Fin b × Fin c

def cells (a b c : Nat) : List (Cell a b c) :=
  (List.finRange a).flatMap fun i =>
    (List.finRange b).flatMap fun j => (List.finRange c).map fun k => (i,j,k)

def holes {a b c : Nat} (ab : List (Fin a × Fin b))
    (ac : List (Fin a × Fin c)) (bc : List (Fin b × Fin c)) : Nat :=
  ((cells a b c).filter fun x =>
    !(ab.contains (x.1,x.2.1) || ac.contains (x.1,x.2.2) || bc.contains x.2)).length

def bound (a b c : Nat) (lb : Nat) : Prop :=
  ∀ (u v : Fin a × Fin b) (w : Fin a × Fin c) (z : Fin b × Fin c),
    lb ≤ holes [u,v] [w] [z]

set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem all_pair_placements : bound 2 2 2 1 := by unfold bound; simp only [Prod.forall]; decide

theorem can_leave_one : ∃ (u v w z : Fin 2 × Fin 2),
    holes [u,v] [w] [z] = 1 := by simp only [Prod.exists]; decide

theorem losing_one_pair :
    (∀ (u w z : Fin 2 × Fin 2), 2 ≤ holes [u] [w] [z]) ∧
    (∀ (u v z : Fin 2 × Fin 2), 2 ≤ holes [u,v] [] [z]) ∧
    (∀ (u v w : Fin 2 × Fin 2), 2 ≤ holes [u,v] [w] []) := by simp only [Prod.forall]; decide

theorem losing_one_unary : bound 3 2 2 2 ∧ bound 2 3 2 2 ∧ bound 2 2 3 2 := by
  unfold bound
  simp only [Prod.forall]
  decide

#print axioms all_pair_placements
#print axioms can_leave_one
#print axioms losing_one_pair
#print axioms losing_one_unary
end ThreePrimeBox
