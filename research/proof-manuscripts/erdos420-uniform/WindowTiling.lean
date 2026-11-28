import Std

/-! Uniform short-window occupancy gives a lower bound in every longer window.
C is the cumulative count at a fixed threshold. The predicate tested at each
site is allowed to depend on the starting threshold n, but stays fixed across
all subintervals within this invocation. -/
namespace WindowTiling

theorem tile (C : Nat → Nat) (mono : ∀ a b, a ≤ b → C a ≤ C b)
    (n H L m : Nat)
    (step : ∀ x, n ≤ x → x + L ≤ n + H → C x + m ≤ C (x + L)) :
    C n + (H / L) * m ≤ C (n + H) := by
  have cover (k : Nat) (hk : k * L ≤ H) : C n + k * m ≤ C (n + k * L) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul] at hk
      have prev := ih (by omega)
      have inc := step (n + k * L) (by omega) (by omega)
      rw [Nat.succ_mul, Nat.succ_mul]
      rw [Nat.add_assoc n (k * L) L] at inc
      omega
  have bound := Nat.div_mul_le_self H L
  exact Nat.le_trans (cover (H/L) bound) (mono _ _ (by omega))

/-- Windows of variable length at most L can be used in the fixed tiling. -/
theorem tile_variable (C : Nat → Nat) (mono : ∀ a b, a ≤ b → C a ≤ C b)
    (length : Nat → Nat) (n H L m : Nat)
    (short : ∀ x, n ≤ x → x + L ≤ n + H →
      length x ≤ L ∧ C x + m ≤ C (x + length x)) :
    C n + (H / L) * m ≤ C (n + H) := by
  apply tile C mono
  intro x lo hi
  obtain ⟨hL, hg⟩ := short x lo hi
  exact Nat.le_trans hg (mono _ _ (by omega))

end WindowTiling
