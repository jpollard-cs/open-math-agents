import Std

/-! The free-reassignment cut criterion on a product of finite alphabets.
The logical core in fact needs no finiteness assumption. -/
namespace CanonicalCut

variable {V R : Type} {A : V → Type}
abbrev Point (A : V → Type) := (i : V) → A i

def agrees (U : V → Prop) (x y : Point A) : Prop :=
  ∀ i, U i → x i = y i

def internal (s : R → V → Prop) (U : V → Prop) (r : R) : Prop :=
  ∀ i, s r i → U i

def oneHole (s : R → V → Prop) (U : V → Prop) (z : Point A) : Prop :=
  ∃ f : R → Point A, ∀ x, ¬ agrees U x z →
    ∃ r, internal s U r ∧ agrees (s r) x (f r)

def closed (s : R → V → Prop) (w : R → Point A) (z : Point A) (U : V → Prop) : Prop :=
  ∀ r i, s r i → w r i ≠ z i → U i → internal s U r

theorem oneHole_iff_closed
    (s : R → V → Prop) (terminal U : V → Prop) (z : Point A) (w : R → Point A)
    (inside : ∀ i, U i → terminal i)
    (priv : ∀ r, ¬ agrees (s r) z (w r))
    (cover : ∀ x, agrees terminal x z ∨ ∃ r, agrees (s r) x (w r))
    (essential : ∀ (d : R) (f : R → Point A), ¬ (∀ x, agrees terminal x z ∨
        ∃ r, r ≠ d ∧ agrees (s r) x (f r))) :
    oneHole s U z ↔ closed s w z U := by
  classical
  constructor
  · rintro ⟨f, hf⟩ d i hsi hne hui
    apply Classical.byContradiction
    intro hd
    let g : R → Point A := fun r => if internal s U r then f r else w r
    apply essential d g
    intro x
    by_cases old : agrees U x z
    · rcases cover x with ht | ⟨r, hr⟩
      · exact Or.inl ht
      · right
        have hout : ¬ internal s U r := by
          intro hin
          apply priv r
          intro j hj
          exact (old j (hin j hj)).symm.trans (hr j hj)
        have hrd : r ≠ d := by
          intro eq
          subst r
          exact hne ((hr i hsi).symm.trans (old i hui))
        exact ⟨r, hrd, by simpa [g, hout] using hr⟩
    · obtain ⟨r, hin, hr⟩ := hf x old
      exact Or.inr ⟨r, fun eq => hd (eq ▸ hin), by simpa [g, hin] using hr⟩
  · intro hc
    refine ⟨w, ?_⟩
    intro x hx
    let y : Point A := fun i => if U i then x i else z i
    have hterm : ¬ agrees terminal y z := by
      intro he
      apply hx
      intro i hi
      simpa [y, hi] using he i (inside i hi)
    obtain ⟨r, hr⟩ := (cover y).resolve_left hterm
    have hsome : ∃ i, s r i ∧ w r i ≠ z i := by
      apply Classical.byContradiction
      intro hn
      apply priv r
      intro i hi
      symm
      apply Classical.byContradiction
      intro hnz
      exact hn ⟨i, hi, hnz⟩
    obtain ⟨i, hsi, hdiff⟩ := hsome
    have hui : U i := by
      apply Classical.byContradiction
      intro hu
      exact hdiff (by simpa [y, hu] using (hr i hsi).symm)
    have hin := hc r i hsi hdiff hui
    exact ⟨r, hin, fun j hj => by simpa [y, hin j hj] using hr j hj⟩

#print axioms oneHole_iff_closed
end CanonicalCut
