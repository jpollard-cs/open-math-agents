/- AI-authored. Cover certificates for distinct nontrivial divisor moduli. -/
namespace CoverTower
abbrev Row := Nat × Nat
abbrev Level := Nat × List Row

def hits (a step : Nat) (r : Row) : Bool := step % r.1 == 0 && a % r.1 == r.2

def test : List Level → Nat → Nat → Bool
  | [], _, _ => false
  | (q, rs) :: more, a, step =>
    rs.any (hits a step) ||
      (q != 0 && (List.range q).all (fun i => test more (a + step*i) (step*q)))

def rows (stages : List Level) := stages.flatMap Prod.snd

theorem sound (stages : List Level) (a step : Nat) (h : test stages a step = true) (k : Nat) :
    ∃ r ∈ rows stages, (a+step*k) % r.1 = r.2 := by
  induction stages generalizing a step k with
  | nil => simp [test] at h
  | cons s more ih =>
    obtain ⟨q, rs⟩ := s
    simp only [test, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨hq, h⟩
    · obtain ⟨r,hr,ha⟩ := List.any_eq_true.mp h
      simp only [hits, Bool.and_eq_true, beq_iff_eq] at ha
      obtain ⟨d,hd⟩ := Nat.dvd_of_mod_eq_zero ha.1
      refine ⟨r, ?_, ?_⟩
      · simp [rows, hr]
      · rw [hd, Nat.mul_assoc, Nat.add_mul_mod_self_left, ha.2]
    · have hq' : q ≠ 0 := by simpa using hq
      have iok := List.mem_range.mpr (Nat.mod_lt k (Nat.pos_of_ne_zero hq'))
      have hx := List.all_eq_true.mp h (k%q) iok
      obtain ⟨r,hr,ha⟩ := ih (a+step*(k%q)) (step*q) hx (k/q)
      refine ⟨r, ?_, ?_⟩
      · simp [rows] at hr ⊢
        exact Or.inr hr
      · rw [Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.mod_add_div] at ha
        exact ha

theorem allIntegers {stages : List Level} {N : Nat}
    (hN : 0 < N) (hv : test stages 0 1 = true)
    (hd : ∀ r ∈ rows stages, r.1 ∣ N) (x : Int) :
    ∃ r ∈ rows stages, x % (r.1 : Int) = (r.2 : Int) := by
  have hz : 0 ≤ x % (N : Int) := Int.emod_nonneg _ (by omega)
  obtain ⟨r,hr,ha⟩ := sound stages 0 1 hv ((x%(N:Int)).toNat)
  simp only [Nat.one_mul,Nat.zero_add] at ha
  have hc := congrArg (fun u : Nat => (u : Int)) ha
  rw [Int.natCast_emod,Int.toNat_of_nonneg hz,
      Int.emod_emod_of_dvd x (Int.natCast_dvd_natCast.mpr (hd r hr))] at hc
  exact ⟨r,hr,hc⟩
end CoverTower
