import Std

/-! Codex (OpenAI), November 2026. A finite batch is one movable row per
label. The first lemma targets all batches simultaneously. The last gives
the integer form of the joint product inequality by exact double counting. -/
namespace JointBatch

theorem avoidTargets {X I : Type} (q : I → Nat) (V : (b : I) → Fin (q b) → Type)
    (oldHole : X → Prop) (digit : (b : I) → X → Fin (q b))
    (target : I → X → Prop) (hit : (b : I) → (j : Fin (q b)) → V b j → X → Prop)
    (aim : ∀ b j, ∃ v, ∀ x, target b x → digit b x = j → hit b j v x)
    (escape : ∀ f : (b : I) → (j : Fin (q b)) → V b j,
      ∃ x, oldHole x ∧ ∀ b j, ¬hit b j (f b j) x) :
    ∃ x, oldHole x ∧ ∀ b, ¬target b x := by
  classical
  let f (b : I) (j : Fin (q b)) := Classical.choose (aim b j)
  obtain ⟨x, hx, misses⟩ := escape f
  refine ⟨x, hx, fun b hb => misses b (digit b x) ?_⟩
  exact Classical.choose_spec (aim b (digit b x)) x hb rfl

private def total : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n+1, f => total n f + f n

private theorem totalAdd (n : Nat) (f g : Nat → Nat) :
    total n (fun j => f j + g j) = total n f + total n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total, ih]; omega

private theorem totalScale (n c : Nat) (f : Nat → Nat) :
    total n (fun j => f j * c) = total n f * c := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp [total, ih, Nat.add_mul]

private theorem totalLower (n c : Nat) (f : Nat → Nat) (h : ∀ j < n, c ≤ f j) :
    n*c ≤ total n f := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    rw [total, Nat.succ_mul]
    exact Nat.add_le_add (ih fun j hj => h j (by omega)) (h n (by omega))

private theorem totalMiss (n t : Nat) :
    total n (fun j => if t = j then 0 else 1) = if t < n then n-1 else n := by
  induction n with
  | zero => simp [total]
  | succ n ih => simp only [total, ih]; split <;> split <;> split <;> omega

structure Column (X : Type) where
  pred : Nat
  value : X → Fin (pred+1)

private def survivors {X : Type} (s : Column X) (h : List X) (j : Nat) : List X :=
  h.filter (fun x => (s.value x).val != j)

private theorem countSurvivors {X : Type} (s : Column X) (h : List X) :
    total (s.pred+1) (fun j => (survivors s h j).length) = h.length*s.pred := by
  induction h with
  | nil =>
    change total (s.pred+1) (fun _ => 0) = 0*s.pred
    have zeroSum (n : Nat) : total n (fun _ => 0) = 0 := by
      induction n with
      | zero => rfl
      | succ n ih => simp [total, ih]
    simp [zeroSum]
  | cons x h ih =>
    have point (j : Nat) : (survivors s (x::h) j).length =
        (survivors s h j).length + (if (s.value x).val = j then 0 else 1) := by
      by_cases hit : (s.value x).val = j <;> simp [survivors, hit]
    simp only [point, totalAdd, ih, totalMiss, (s.value x).isLt, if_true,
      Nat.add_sub_cancel, List.length_cons, Nat.succ_mul]

def choices {X : Type} : List (Column X) → Nat
  | [] => 1
  | s::ss => (s.pred+1) * choices ss

def missChoices {X : Type} : List (Column X) → Nat
  | [] => 1
  | s::ss => s.pred * missChoices ss

/-- Every simultaneous sequence of chosen targets leaves an element. -/
def alwaysEscapes {X : Type} : List (Column X) → List X → Prop
  | [], h => 0 < h.length
  | s::ss, h => ∀ j < s.pred+1, alwaysEscapes ss (survivors s h j)

theorem productBound {X : Type} (ss : List (Column X)) (h : List X)
    (escape : alwaysEscapes ss h) : choices ss ≤ h.length * missChoices ss := by
  induction ss generalizing h with
  | nil =>
    change 0 < h.length at escape
    simp only [choices, missChoices, Nat.mul_one]
    omega
  | cons s ss ih =>
    have each (j : Nat) (hj : j < s.pred+1) := ih _ (escape j hj)
    have bound := totalLower (s.pred+1) (choices ss)
        (fun j => (survivors s h j).length * missChoices ss) each
    rw [totalScale, countSurvivors, Nat.mul_assoc] at bound
    exact bound

#print axioms avoidTargets
#print axioms productBound
end JointBatch
