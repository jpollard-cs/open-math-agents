import Std

/-! Rational thresholds u(n)/v(n); all choices of unused residues are free. -/
namespace DiffuseTrace

def Safe (xs rs : List Nat) : Prop :=
  ∀ f : Nat → Nat, ∃ x ∈ xs, ∀ n ∈ rs, x % n ≠ f n

def freq (xs : List Nat) (n a : Nat) := (xs.filter (fun x => x % n == a)).length
def withoutClass (xs : List Nat) (n a : Nat) := xs.filter fun x => x % n != a

private theorem partition (xs : List Nat) (n a : Nat) :
    (withoutClass xs n a).length + freq xs n a = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : x % n = a <;> simp_all [withoutClass, freq] <;> omega

private theorem safe_step {xs rs : List Nat} (h : Safe xs rs) {n : Nat}
    (hn : n ∈ rs) (a : Nat) : Safe (withoutClass xs n a) (rs.filter (· != n)) := by
  intro f
  obtain ⟨x,hx,ok⟩ := h (fun m => if m=n then a else f m)
  refine ⟨x, List.mem_filter.mpr ⟨hx, ?_⟩, ?_⟩
  · simpa using ok n hn
  · intro m hm
    obtain ⟨hm,hne⟩ := List.mem_filter.mp hm
    simpa [show m ≠ n by simpa using hne] using ok m hm

inductive Run (u v : Nat → Nat) : List Nat → List Nat → List Nat → List Nat → Nat → Nat → Prop
  | stop (xs rs) (done : ∀ n ∈ rs, ∀ a, freq xs n a * u n < xs.length * v n) :
      Run u v xs rs xs rs 1 1
  | step {xs rs ys ts s t} (n a : Nat) (hn : n ∈ rs)
      (heavy : xs.length * v n ≤ freq xs n a * u n)
      (rest : Run u v (withoutClass xs n a) (rs.filter (· != n)) ys ts s t) :
      Run u v xs rs ys ts (u n * s) ((u n - v n) * t)

theorem exists_run (u v : Nat → Nat) (xs rs : List Nat) :
    ∃ ys ts s t, Run u v xs rs ys ts s t := by
  classical
  by_cases h : ∀ n ∈ rs, ∀ a, freq xs n a * u n < xs.length * v n
  · exact ⟨xs, rs, 1, 1, .stop xs rs h⟩
  · simp only [Classical.not_forall] at h
    obtain ⟨n,hn,a,heavy⟩ := h
    have shorter : (rs.filter (· != n)).length < rs.length :=
      List.length_filter_lt_length_iff_exists.mpr ⟨n,hn,by simp⟩
    obtain ⟨ys,ts,s,t,rest⟩ := exists_run u v (withoutClass xs n a) (rs.filter (· != n))
    exact ⟨ys,ts,u n*s,(u n-v n)*t,.step n a hn (by omega) rest⟩
termination_by rs.length

theorem guarantees {u v : Nat → Nat} (threshold : ∀ n, v n ≤ u n)
    {xs rs ys ts s t} (run : Run u v xs rs ys ts s t) (safe : Safe xs rs) :
    Safe ys ts ∧ (∀ n ∈ ts, ∀ a, freq ys n a * u n < ys.length * v n) ∧
    ys.length * s ≤ xs.length * t := by
  induction run with
  | stop xs rs done => exact ⟨safe,done,by simp⟩
  | @step xs rs ys ts s t n a hn heavy rest ih =>
    obtain ⟨safe',done,tail⟩ := ih (safe_step safe hn a)
    have part := partition xs n a
    have split : (withoutClass xs n a).length*u n + freq xs n a*u n = xs.length*u n := by
      rw [← Nat.add_mul,part]
    have split' : xs.length*(u n-v n) + xs.length*v n = xs.length*u n := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (threshold n)]
    have shrink : (withoutClass xs n a).length*u n ≤ xs.length*(u n-v n) := by omega
    refine ⟨safe',done,?_⟩
    calc
      ys.length*(u n*s) = (ys.length*s)*u n := by ac_rfl
      _ ≤ ((withoutClass xs n a).length*t)*u n := Nat.mul_le_mul_right _ tail
      _ = ((withoutClass xs n a).length*u n)*t := by ac_rfl
      _ ≤ (xs.length*(u n-v n))*t := Nat.mul_le_mul_right _ shrink
      _ = _ := by ac_rfl

#print axioms exists_run
#print axioms guarantees
end DiffuseTrace
