import Lean.Elab.Tactic.Omega

/-! The suffix-selection step for a finite list of prime offsets.
Written by Codex (AI) at the request of Jordan Pollard. -/
namespace FactorialDensity

/-- Every intermediate integer is attained by the count in a shrinking suffix. -/
theorem hits_intermediate (s : Nat → Nat) (h r : Nat)
    (initial : r ≤ s 0) (terminal : s h ≤ r)
    (unit_drop : ∀ i, i < h → s i ≤ s (i+1)+1) :
    ∃ i, i ≤ h ∧ s i = r := by
  induction h with
  | zero =>
    exact ⟨0, Nat.le_refl _, by omega⟩
  | succ h ih =>
    by_cases done_h : s h ≤ r
    · obtain ⟨i, hi, hit⟩ := ih done_h (fun j hj => unit_drop j (by omega))
      exact ⟨i, by omega, hit⟩
    · have near := unit_drop h (by omega)
      exact ⟨h+1, Nat.le_refl _, by omega⟩

end FactorialDensity
#print axioms FactorialDensity.hits_intermediate
