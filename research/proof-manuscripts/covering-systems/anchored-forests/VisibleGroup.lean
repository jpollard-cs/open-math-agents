import Std

/-! A group of rows can be aimed independently at joint old and new digit
patterns. If all labels always leave an old hole, the group has fewer rows
than patterns. X can be the integer grid itself. -/
namespace VisibleGroup

theorem capacity {X : Type} {b p t : Nat} (hb : 0 < b) (hp : 0 < p)
    (oldHole : X → Prop) (old : X → Fin b) (inner : X → Fin p)
    (V : Fin t → Type) (hit : (i : Fin t) → V i → X → Prop)
    (aim : ∀ (i : Fin t) (a : Fin b) (c : Fin p), ∃ v, ∀ x, oldHole x →
      old x = a → inner x = c → hit i v x)
    (escape : ∀ (f : (i : Fin t) → V i), ∃ x, oldHole x ∧ ∀ i, ¬ hit i (f i) x) :
    t < b * p := by
  classical
  apply Classical.byContradiction
  intro neg
  have enough : b * p ≤ t := Nat.le_of_not_gt neg
  let first (i : Fin t) : Fin b := ⟨i.val / p % b, Nat.mod_lt _ hb⟩
  let second (i : Fin t) : Fin p := ⟨i.val % p, Nat.mod_lt _ hp⟩
  let f (i : Fin t) := Classical.choose (aim i (first i) (second i))
  obtain ⟨x, hx, escaped⟩ := escape f
  let a := old x
  let c := inner x
  have under : p * a.val + c.val < b * p := calc
    p * a.val + c.val < p * a.val + p := Nat.add_lt_add_left c.isLt _
    _ = p * (a.val + 1) := (Nat.mul_succ p a.val).symm
    _ ≤ p * b := Nat.mul_le_mul_left p a.isLt
    _ = b * p := Nat.mul_comm _ _
  let i : Fin t := ⟨p * a.val + c.val, Nat.lt_of_lt_of_le under enough⟩
  apply escaped i
  apply Classical.choose_spec (aim i (first i) (second i)) x hx
  · apply Fin.ext
    change a.val = (p * a.val + c.val) / p % b
    simp [Nat.mul_add_div hp, Nat.div_eq_of_lt c.isLt, Nat.mod_eq_of_lt a.isLt]
  · apply Fin.ext
    change c.val = (p * a.val + c.val) % p
    simp [Nat.mod_eq_of_lt c.isLt]

#print axioms capacity
end VisibleGroup
