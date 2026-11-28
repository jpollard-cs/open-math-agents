import JointBatch

/-! Codex (OpenAI). Integer congruences that cover a target fibre by lifting
an arbitrary covering system on its quotient coordinate. Multiple batches
may share coordinates. The quotient moduli may repeat. -/
namespace IntegerBatch

structure Batch where
  guard : Int
  size : Nat
  modulus : Fin size → Int
  quotient : Fin size → Int
  label : Fin size → Int
  divides : ∀ i, modulus i ∣ guard * quotient i
  cover : ∀ s : Int, ∃ i, quotient i ∣ s - label i

/-- All integers in the target congruence class are covered by an explicit
placement of the original integer rows. -/
theorem coverFibre (b : Batch) (target x : Int) (inside : b.guard ∣ x - target) :
    ∃ i, b.modulus i ∣ x - (target + b.guard * b.label i) := by
  obtain ⟨s, hs⟩ := inside
  obtain ⟨i, z, hz⟩ := b.cover s
  obtain ⟨a, ha⟩ := b.divides i
  refine ⟨i, a*z, ?_⟩
  calc
    x - (target + b.guard * b.label i)
        = b.guard * s - b.guard * b.label i := by omega
    _ = b.guard * (s - b.label i) := (Int.mul_sub ..).symm
    _ = (b.guard * b.quotient i)*z := by rw [hz, Int.mul_assoc]
    _ = b.modulus i * (a*z) := by rw [ha, Int.mul_assoc]

/-- Fix every complementary row and omit a reserved row. If no reassignment of
the disjoint batches finishes a cover, every joint choice of integer target
classes misses some integer that escaped the complement. -/
theorem avoidIntegerTargets {I : Type} (bs : I → Batch) (oldHole : Int → Prop)
    (escape : ∀ f : (i : I) → Fin (bs i).size → Int,
      ∃ x, oldHole x ∧ ∀ i j, ¬ (bs i).modulus j ∣ x - f i j)
    (target : I → Int) :
    ∃ x, oldHole x ∧ ∀ i, ¬ (bs i).guard ∣ x - target i := by
  let f (i : I) (j : Fin (bs i).size) := target i + (bs i).guard * (bs i).label j
  obtain ⟨x,hx,miss⟩ := escape f
  refine ⟨x,hx,fun i hi => ?_⟩
  obtain ⟨j,hj⟩ := coverFibre (bs i) (target i) x hi
  exact miss i j hj

private theorem escapesOfFunctions {I X : Type} [DecidableEq I]
    (col : I → JointBatch.Column X) (keys : List I) (uniq : keys.Nodup) (hs : List X)
    (existsMiss : ∀ f : I → Nat, ∃ x ∈ hs,
      ∀ i ∈ keys, ((col i).value x).val ≠ f i) :
    JointBatch.alwaysEscapes (keys.map col) hs := by
  induction keys generalizing hs with
  | nil =>
    obtain ⟨x,hx,_⟩ := existsMiss (fun _ => 0)
    exact List.length_pos_of_mem hx
  | cons i rest ih =>
    have hno := List.nodup_cons.mp uniq
    intro j _
    apply ih hno.2
    intro f
    let updated (u : I) : Nat := if u = i then j else f u
    obtain ⟨x,hx,miss⟩ := existsMiss updated
    have headMiss : ((col i).value x).val ≠ j := by
      simpa [updated] using miss i List.mem_cons_self
    refine ⟨x, List.mem_filter.mpr ⟨hx, ?_⟩, ?_⟩
    · simpa using headMiss
    · intro u hu
      have hne : u ≠ i := fun e => hno.1 (e ▸ hu)
      simpa [updated, hne] using miss u (List.mem_cons_of_mem _ hu)

/-- The integer joint product bound. hs can contain one representative per
joint visible pattern. A column enumerates the observed residues for its
batch, and representative records the congruences of each true old hole. -/
theorem integerProductBound {I : Type} [DecidableEq I] (keys : List I) (uniq : keys.Nodup)
    (bs : I → Batch) (oldHole : Int → Prop) (hs : List Int)
    (col : I → JointBatch.Column Int) (marker : I → Nat → Int)
    (representative : ∀ z, oldHole z → ∃ y ∈ hs, ∀ i ∈ keys,
        (bs i).guard ∣ z - marker i ((col i).value y).val)
    (escape : ∀ f : (i : I) → Fin (bs i).size → Int,
      ∃ x, oldHole x ∧ ∀ i j, ¬ (bs i).modulus j ∣ x - f i j) :
    JointBatch.choices (keys.map col) ≤ hs.length * JointBatch.missChoices (keys.map col) := by
  apply JointBatch.productBound
  apply escapesOfFunctions col keys uniq
  intro f
  obtain ⟨z,hz,miss⟩ := avoidIntegerTargets bs oldHole escape (fun i => marker i (f i))
  obtain ⟨y,hy,repr⟩ := representative z hz
  refine ⟨y,hy,fun i hi he => ?_⟩
  exact miss i (he ▸ repr i hi)

#print axioms integerProductBound
#print axioms coverFibre
#print axioms avoidIntegerTargets
end IntegerBatch
