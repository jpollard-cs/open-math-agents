import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace CompleteShells

def energy : List ℕ → ℕ
  | [] => 0
  | a :: as => a * a + energy as

/-- A coordinatewise (possibly constant) arithmetic progression in the
nonnegative lattice. The constructors require all three lists to have equal length. -/
inductive Mid : List ℕ → List ℕ → List ℕ → Prop
  | nil : Mid [] [] []
  | cons {a b c : ℕ} {x y z : List ℕ} (h : a + c = 2 * b) (hs : Mid x y z) :
      Mid (a :: x) (b :: y) (c :: z)

private theorem scalar_gap {a b c : ℕ} (hm : a + c = 2 * b) (hn : a ≠ c) :
    2 * (b*b) + 2 ≤ a*a + c*c := by
  have aux (u v w : ℕ) (hp : u+w=2*v) (hlt : u<w) : 2*(v*v)+2 ≤ u*u+w*w := by
    have hv : u < v := by omega
    obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le (show u+1 ≤ v by omega)
    have hw : w = u+2+2*k := by omega
    rw [hk,hw]
    nlinarith
  rcases Nat.lt_or_gt_of_ne hn with h | h
  · exact aux a b c hm h
  · have ht := aux c b a (by omega) h
    omega

private theorem gap {x y z : List ℕ} (h : Mid x y z) :
    (x = y ∧ z = y) ∨
    (2 * energy y + 2 ≤ energy x + energy z ∧
      (energy x ≠ energy z ∨ 2 * energy y + 4 ≤ energy x + energy z)) := by
  induction h with
  | nil => exact Or.inl ⟨rfl,rfl⟩
  | @cons a b c x y z hm _ ih =>
    by_cases hac : a = c
    · have hab : a = b := by omega
      subst c
      subst b
      rcases ih with ⟨rfl,rfl⟩ | ⟨hg, hd | hd⟩
      · exact Or.inl ⟨rfl,rfl⟩
      · right; simp only [energy]; omega
      · right; simp only [energy]; omega
    · have hg := scalar_gap hm hac
      have hs : a*a ≠ c*c := by
        rcases Nat.lt_or_gt_of_ne hac with ht | ht
        · have := Nat.mul_self_lt_mul_self ht
          omega
        · have := Nat.mul_self_lt_mul_self ht
          omega
      rcases ih with ⟨rfl,rfl⟩ | ⟨ht,_⟩
      · right; simp only [energy]; omega
      · right; simp only [energy]; omega

/-- The union of two consecutive squared-norm shells contains no proper
three-term progression in any dimension or nonnegative digit box. -/
theorem adjacent {r : ℕ} {x y z : List ℕ} (hm : Mid x y z)
    (hx : r ≤ energy x ∧ energy x ≤ r+1)
    (hy : r ≤ energy y ∧ energy y ≤ r+1)
    (hz : r ≤ energy z ∧ energy z ≤ r+1) : x = y ∧ z = y := by
  rcases gap hm with h | ⟨ha,hb | hb⟩
  · exact h
  · omega
  · omega

#print axioms adjacent
end CompleteShells
