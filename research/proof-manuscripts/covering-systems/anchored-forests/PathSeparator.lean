import Std

/-! Missing pairs on two sides of a separating digit. The lists may include
duplicates. Both endpoints may change. -/
namespace PathSeparator

abbrev Cell := Nat × Nat

def atEndpoint (rows : List Cell) (a : Nat) : List Nat :=
  (rows.filter (fun t => t.1 == a)).map Prod.snd

def middle (d : Nat) (l r : List Cell) (a b : Nat) : List Nat :=
  (List.range d).filter (fun i =>
     !(atEndpoint l a).contains i && !(atEndpoint r b).contains i)

theorem fibreCost (d : Nat) (l r : List Cell) (a b : Nat) :
    d ≤ (middle d l r a b).length + (atEndpoint l a).length +
      (atEndpoint r b).length := by
  have inclusion : List.range d ⊆ middle d l r a b ++ atEndpoint l a ++ atEndpoint r b := by
    intro i hi
    by_cases hl : i ∈ atEndpoint l a
    · simp [hl]
    by_cases hr : i ∈ atEndpoint r b
    · simp [hr]
    have hm : i ∈ middle d l r a b := List.mem_filter.mpr ⟨hi, by simp [hl,hr]⟩
    simp [hm]
  simpa [Nat.add_assoc] using List.nodup_range.length_le_of_subset inclusion

theorem separateCost (rows : List Cell) {a x : Nat} (h : a ≠ x) :
    (atEndpoint rows a).length + (atEndpoint rows x).length ≤ rows.length := by
  induction rows with
  | nil => simp [atEndpoint]
  | cons c rows ih =>
    have ih' := ih
    simp only [atEndpoint, List.length_map] at ih' ⊢
    by_cases ha : c.1 = a
    · simp [ha,h] at *
      omega
    · by_cases hx : c.1 = x
      · simp [hx,Ne.symm h] at *
        omega
      · simp [ha,hx] at *
        omega

/-- Pinching one fibre to size one forces other endpoint pairs to extend.
The quantitative inequality retains the exact cost for larger fibres too. -/
theorem twoFibre (d : Nat) (l r : List Cell) {a b x y : Nat}
    (ha : a ≠ x) (hb : b ≠ y) :
    2*d ≤ (middle d l r a b).length + (middle d l r x y).length +
      l.length + r.length := by
  have h₁ := fibreCost d l r a b
  have h₂ := fibreCost d l r x y
  have h₃ := separateCost l ha
  have h₄ := separateCost r hb
  omega

theorem offCross (d : Nat) (l r : List Cell) {a b x y : Nat}
    (hl : l.length < d) (hr : r.length < d)
    (hs : (middle d l r a b).length ≤ 1) (ha : a ≠ x) (hb : b ≠ y) :
    0 < (middle d l r x y).length := by
  have := twoFibre d l r ha hb
  omega

#print axioms offCross
end PathSeparator
