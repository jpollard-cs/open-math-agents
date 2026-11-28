import Lean.Elab.Tactic.Omega

/-! The exact forbidden translation vectors for the T family. Codex (AI). -/
namespace PolyominoT

def shape (w h x y : Int) : Prop :=
  (x = 0 ∧ 0 ≤ y ∧ y ≤ 2*h-2) ∨ (0 ≤ x ∧ x < w ∧ y = h-1)

def overlaps (w h dx dy : Int) : Prop :=
  ∃ x y, shape w h x y ∧ shape w h (x+dx) (y+dy)

/-- Differences of the w-by-h rectangle, with only the extra vertical bar. -/
theorem forbidden (w h dx dy : Int) (hw : 2 ≤ w) (hh : 2 ≤ h) :
    overlaps w h dx dy ↔
      (-w < dx ∧ dx < w ∧ -h < dy ∧ dy < h) ∨
      (dx = 0 ∧ -(2*h-2) ≤ dy ∧ dy ≤ 2*h-2) := by
  constructor
  · rintro ⟨x,y,h₁,h₂⟩
    rcases h₁ with a | a <;> rcases h₂ with b | b <;> omega
  · intro hyp
    rcases hyp with box | bar
    · by_cases pos : 0 ≤ dx
      · refine ⟨0,h-1-dy,Or.inl ?_,Or.inr ?_⟩ <;> omega
      · refine ⟨-dx,h-1,Or.inr ?_,Or.inl ?_⟩ <;> omega
    · by_cases pos : 0 ≤ dy
      · refine ⟨0,0,Or.inl ?_,Or.inl ?_⟩ <;> omega
      · refine ⟨0,-dy,Or.inl ?_,Or.inl ?_⟩ <;> omega

end PolyominoT
#print axioms PolyominoT.forbidden
