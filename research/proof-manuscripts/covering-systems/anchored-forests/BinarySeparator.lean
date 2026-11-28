import Std

/- Codex (OpenAI). Finite multiplicity statements for a binary by q separator. -/
namespace BinarySeparator

structure Counts where
  empty : Nat
  top : Nat
  bottom : Nat
  both : Nat

def Counts.total (a : Counts) := a.empty + a.top + a.bottom + a.both

/-- Entries of the transportation table at exactly the nine allowed zero-overlap pairs. -/
def DisjointTransport (a b : Counts) : Prop :=
  ∃ x00 x01 x02 x03 x10 x12 x20 x21 x30 : Nat,
    x00 + x01 + x02 + x03 = a.empty ∧
    x10 + x12 = a.top ∧ x20 + x21 = a.bottom ∧ x30 = a.both ∧
    x00 + x10 + x20 + x30 = b.empty ∧
    x01 + x21 = b.top ∧ x02 + x12 = b.bottom ∧ x03 = b.both

def Conditions (a b : Counts) : Prop :=
  a.both ≤ b.empty ∧ a.both + a.top ≤ b.empty + b.bottom ∧
  a.both + a.bottom ≤ b.empty + b.top ∧ b.both ≤ a.empty

theorem transport_iff (a b : Counts) (balanced : a.total = b.total) :
    DisjointTransport a b ↔ Conditions a b := by
  unfold Counts.total at balanced
  constructor
  · rintro ⟨x00,x01,x02,x03,x10,x12,x20,x21,x30,h0,h1,h2,h3,g0,g1,g2,g3⟩
    unfold Conditions
    omega
  · rintro ⟨h3,h1,h2,h0⟩
    let x12 := min a.top b.bottom
    let x21 := min a.bottom b.top
    let x10 := a.top - x12
    let x20 := a.bottom - x21
    refine ⟨b.empty - (x10+x20+a.both), b.top-x21, b.bottom-x12, b.both,
        x10, x12, x20, x21, a.both, ?_⟩
    dsimp only [x10, x20, x12, x21]
    cases Nat.le_total a.top b.bottom with
    | inl h =>
      rw [Nat.min_eq_left h]
      cases Nat.le_total a.bottom b.top with
      | inl h' => rw [Nat.min_eq_left h']; omega
      | inr h' => rw [Nat.min_eq_right h']; omega
    | inr h =>
      rw [Nat.min_eq_right h]
      cases Nat.le_total a.bottom b.top with
      | inl h' => rw [Nat.min_eq_left h']; omega
      | inr h' => rw [Nat.min_eq_right h']; omega

/-- The remaining cells in the two rows can fit all horizontal pairs. -/
theorem horizontal_split (available count : Nat) :
    (∃ inTop inBottom : Nat, inTop + inBottom = count ∧
       2 * inTop ≤ available ∧ 2 * inBottom ≤ available) ↔
       count ≤ 2 * (available / 2) := by
  constructor
  · rintro ⟨a,b,h,ha,hb⟩
    omega
  · intro h
    refine ⟨min count (available / 2), count - min count (available / 2), ?_⟩
    cases Nat.le_total count (available / 2) with
    | inl ht => rw [Nat.min_eq_left ht]; omega
    | inr ht => rw [Nat.min_eq_right ht]; omega

/-- For at most q-1 prescribed types, neither the horizontal parity condition
    nor the one-column diagonal obstruction can prevent a placement. -/
theorem room_for_pairs (q vertical horizontal diagonal : Nat)
    (h : vertical + horizontal + diagonal < q) :
    vertical ≤ q ∧ diagonal ≤ q-vertical ∧
    horizontal ≤ 2*((q-vertical-diagonal)/2) ∧
    ¬ (q-vertical = 1 ∧ diagonal = 1) := by omega

#print axioms transport_iff
#print axioms horizontal_split
#print axioms room_for_pairs
end BinarySeparator
