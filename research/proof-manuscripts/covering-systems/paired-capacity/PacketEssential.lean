import PacketCoverage

namespace PacketEssential

def Has (n : Nat) (a : Option Int) (x : Int) : Prop :=
  ∃ t, a = some t ∧ (n : Int) ∣ x - t

def Outside (ns : List Nat) (f : Nat → Option Int) (x : Int) : Prop :=
  ∃ n ∈ ns, Has n (f n) x

def Rigid (ns : List Nat) (d : Nat) : Prop :=
  ∀ (f : Nat → Option Int) (v : Option Int),
    (∀ x : Int, Outside ns f x ∨ Has d v x) →
    (∀ n ∈ ns, f n ≠ none) ∧ v ≠ none

theorem all_used {r : Nat} (H : Fin r → Fin r → Prop)
    (cover : ∀ t, ∃ i, H i t)
    (one : ∀ i j k, H i j → H i k → j = k) (i : Fin r) :
    ∃ t, H i t := by
  classical
  let f := fun t => Classical.choose (cover t)
  have hf (t) : H (f t) t := Classical.choose_spec (cover t)
  apply Classical.byContradiction
  intro hn
  have nd : ((List.finRange r).map f).Nodup :=
    (List.nodup_finRange r).map f (fun a b hab he => hab (one (f a) a b (hf a) (he ▸ hf b)))
  have missing : i ∉ (List.finRange r).map f := by
    intro h
    obtain ⟨a,_,ha⟩ := List.mem_map.mp h
    exact hn ⟨a,ha ▸ hf a⟩
  have big := (List.nodup_cons.mpr ⟨missing,nd⟩).length_le_of_subset
    (l₂ := List.finRange r) (fun {j} _ => List.mem_finRange j)
  simp at big
  omega

theorem lcm_common {n m : Nat} {x : Int} (hn : (n : Int) ∣ x) (hm : (m : Int) ∣ x) :
    (n.lcm m : Int) ∣ x :=
  Int.ofNat_dvd_left.mpr (Nat.lcm_dvd (Int.ofNat_dvd_left.mp hn) (Int.ofNat_dvd_left.mp hm))

theorem one_lift {n L r : Nat} (pos : 0 < L) (hl : n.lcm L = L*r)
    (a : Option Int) (x : Int) (j k : Fin r)
    (hj : Has n a (x + (L : Int)*j.val)) (hk : Has n a (x + (L : Int)*k.val)) :
    j = k := by
  obtain ⟨v, hv, h1⟩ := hj
  obtain ⟨w, hw, h2⟩ := hk
  have eq : v=w := Option.some.inj (hv.symm.trans hw)
  subst w
  have h3 := Int.dvd_sub h1 h2
  have h4 : (n : Int) ∣ (L : Int)*((j.val : Int)-k.val) := by
    rw [Int.mul_sub]
    rwa [show x + (L : Int)*j.val - v - (x + (L : Int)*k.val - v) = (L : Int)*j.val - (L : Int)*k.val by omega] at h3
  have h5 := lcm_common h4 (Int.dvd_mul_right (L : Int) ((j.val : Int)-k.val))
  rw [hl,Int.natCast_mul] at h5
  have h6 := (Int.mul_dvd_mul_iff_left (a := (L : Int)) (by omega)).mp h5
  have he := Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h6)
  have jlt : (j.val : Int)<r := by omega
  have klt : (k.val : Int)<r := by omega
  rw [Int.emod_eq_of_lt (by omega) jlt, Int.emod_eq_of_lt (by omega) klt] at he
  exact Fin.ext (by omega)


def proj (L : Nat) (ns : List Nat) : Nat :=
  ns.foldr (fun n t => (Nat.gcd n L).lcm t) 1

theorem proj_dvd {L : Nat} {ns : List Nat} {x : Int}
    (h : ∀ n ∈ ns, (n.gcd L : Int) ∣ x) : (proj L ns : Int) ∣ x := by
  induction ns with
  | nil => exact Int.one_dvd x
  | cons n ns ih =>
    exact lcm_common (h n (by simp)) (ih (fun a ha => h a (by simp [ha])))

theorem shift_project {n L : Nat} {a : Option Int} {x : Int} {t : Nat}
    (h : Has n a (x+(L : Int)*t)) :
    ∃ v, a = some v ∧ (n.gcd L : Int) ∣ x-v := by
  obtain ⟨v,ha,hd⟩ := h
  refine ⟨v,ha,?_⟩
  have u := Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.gcd_dvd_left n L)) hd
  have w := Int.dvd_trans (Int.ofNat_dvd.mpr (Nat.gcd_dvd_right n L))
    (Int.dvd_mul_right (L : Int) (t : Int))
  have := Int.dvd_sub u w
  rwa [show x+(L : Int)*t-v-(L : Int)*t = x-v by omega] at this

theorem contract {L : Nat} (pos : 0<L) (rows : List (Nat × Option Int))
    (A : Int → Prop) (periodic : ∀ x (t : Nat), A (x+(L : Int)*t) → A x)
    (x₀ : Int) (hole : ¬A x₀)
    (periods : ∀ e ∈ rows, e.1.lcm L = L*rows.length)
    (cover : ∀ x, A x ∨ ∃ e ∈ rows, Has e.1 e.2 x) :
    (∀ e ∈ rows, e.2 ≠ none) ∧
    ∀ x, ¬A x → (proj L (rows.map Prod.fst) : Int) ∣ x-x₀ := by
  have project {x : Int} (hx : ¬A x) (e) (he : e ∈ rows) :
      ∃ v, e.2 = some v ∧ (e.1.gcd L : Int) ∣ x-v := by
    let H := fun (i t : Fin rows.length) =>
      Has rows[i.val].1 rows[i.val].2 (x+(L : Int)*t.val)
    have hc (t : Fin rows.length) : ∃ i, H i t := by
      rcases cover (x+(L : Int)*t.val) with h | ⟨a,ha,hit⟩
      · exact False.elim (hx (periodic x t.val h))
      · obtain ⟨i,hi,eq⟩ := List.getElem_of_mem ha
        rw [← eq] at hit
        exact ⟨⟨i,hi⟩,hit⟩
    obtain ⟨i,hi,eq⟩ := List.getElem_of_mem he
    obtain ⟨t,ht⟩ := all_used H hc (fun j a b ha hb =>
      one_lift pos (periods _ (List.getElem_mem j.isLt)) _ _ a b ha hb) ⟨i,hi⟩
    have sol := shift_project ht
    simpa [eq] using sol
  constructor
  · intro e he hn
    obtain ⟨v,h,_⟩ := project hole e he
    simp [hn] at h
  · intro x hx
    apply proj_dvd
    intro n hn
    obtain ⟨e,he,eq⟩ := List.mem_map.mp hn
    subst n
    obtain ⟨v,h,u⟩ := project hx e he
    obtain ⟨w,h',u'⟩ := project hole e he
    have eq := Option.some.inj (h.symm.trans h')
    subst w
    have := Int.dvd_sub u u'
    rwa [show x-v-(x₀-v)=x-x₀ by omega] at this


theorem rigid_step {L d c : Nat} {ns pre : List Nat} (pos : 0<L)
    (div : ∀ n ∈ pre, n ∣ L) (old : Rigid pre d)
    (periods : ∀ n ∈ c :: ns, n.lcm L = L*(ns.length+1))
    (gc : proj L (c::ns) = d) : Rigid (ns++pre) c := by
  intro f v covers
  classical
  have hole : ∃ x, ¬ Outside pre f x := by
    apply Classical.byContradiction
    intro h
    have everywhere (x : Int) : Outside pre f x :=
      Classical.byContradiction fun hx => h ⟨x,hx⟩
    exact (old f none (fun x => Or.inl (everywhere x))).2 rfl
  obtain ⟨x₀,hx₀⟩ := hole
  let rows := (c,v) :: ns.map (fun n => (n,f n))
  have len : rows.length = ns.length+1 := by simp [rows]
  have listed : rows.map Prod.fst = c::ns := by simp [rows,List.map_map,Function.comp_def]
  have allper (e) (he : e ∈ rows) : e.1.lcm L = L*rows.length := by
    rw [len]; apply periods
    rw [← listed]; exact List.mem_map.mpr ⟨e,he,rfl⟩
  have cov (x : Int) : Outside pre f x ∨ ∃ e ∈ rows, Has e.1 e.2 x := by
    rcases covers x with ⟨n,hn,hit⟩|hit
    · rcases List.mem_append.mp hn with hn|hn
      · exact Or.inr ⟨(n,f n),by exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨n,hn,rfl⟩),hit⟩
      · exact Or.inl ⟨n,hn,hit⟩
    · exact Or.inr ⟨(c,v),by simp [rows],hit⟩
  have periodic (x : Int) (t : Nat) (h : Outside pre f (x+(L : Int)*t)) : Outside pre f x := by
    obtain ⟨n,hn,v',ha,hd⟩ := h
    refine ⟨n,hn,v',ha,?_⟩
    have hL := Int.dvd_trans (Int.ofNat_dvd.mpr (div n hn)) (Int.dvd_mul_right (L : Int) (t : Int))
    have := Int.dvd_sub hd hL
    rwa [show x+(L : Int)*t-v'-(L : Int)*t=x-v' by omega] at this
  obtain ⟨used,congruence⟩ := contract pos rows _ periodic x₀ hx₀ allper cov
  rw [listed,gc] at congruence
  have survives := old f (some x₀) (fun x => by
    by_cases h : Outside pre f x
    · exact Or.inl h
    · exact Or.inr ⟨x₀,rfl,congruence x h⟩)
  refine ⟨?_,used (c,v) (by simp [rows])⟩
  intro n hn
  rcases List.mem_append.mp hn with hn|hn
  · exact used (n,f n) (by exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨n,hn,rfl⟩))
  · exact survives.1 n hn

def StrictValid (L d : Nat) : List (List Nat) → Bool
  | [] => true
  | [] :: _ => false
  | (c :: ns) :: rest =>
    ((c::ns).all (fun n => n.lcm L == L*(ns.length+1)) &&
      proj L (c::ns) == d) && StrictValid (L*(ns.length+1)) c rest

def Flat (d : Nat) : List (List Nat) → List Nat
  | [] => [d]
  | [] :: _ => []
  | (c::ns)::rest => ns ++ Flat c rest

theorem chain {stages : List (List Nat)} {pre : List Nat} {L d : Nat}
    (pos : 0<L) (div : ∀ n ∈ pre, n ∣ L) (old : Rigid pre d)
    (cert : StrictValid L d stages = true)
    (f : Nat → Option Int) (cover : ∀x, Outside (Flat d stages++pre) f x) :
    ∀ n ∈ Flat d stages++pre, f n ≠ none := by
  induction stages generalizing pre L d with
  | nil =>
    have h := old f (f d) (fun x => by
      obtain ⟨n,hn,hit⟩ := cover x
      simp only [Flat,List.singleton_append,List.mem_cons] at hn
      rcases hn with rfl|hn
      · exact Or.inr hit
      · exact Or.inl ⟨n,hn,hit⟩)
    intro n hn
    simp only [Flat,List.singleton_append,List.mem_cons] at hn
    exact hn.elim (fun eq => eq ▸ h.2) (h.1 n)
  | cons rows rest ih =>
    cases rows with
    | nil => simp [StrictValid] at cert
    | cons c ns =>
      simp only [StrictValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at cert
      obtain ⟨⟨hp,hg⟩,hc⟩ := cert
      have new := rigid_step pos div old hp hg
      have nd (n) (hn : n ∈ ns++pre) : n ∣ L*(ns.length+1) := by
        rcases List.mem_append.mp hn with hn|hn
        · rw [← hp n (by simp [hn])]
          exact Nat.dvd_lcm_left .. 
        · exact Nat.dvd_trans (div n hn) (Nat.dvd_mul_right ..)
      have perm (n) : n ∈ Flat c rest ++ (ns++pre) ↔ n ∈ Flat d ((c::ns)::rest)++pre := by
        simp only [Flat,List.mem_append]; grind
      have final := ih (Nat.mul_pos pos (by omega)) nd new hc (fun x => by
        obtain ⟨n,hn,hit⟩ := cover x
        exact ⟨n,(perm n).mpr hn,hit⟩)
      exact fun n hn => final n ((perm n).mpr hn)

theorem essential {stages : List (List Nat)} (h : StrictValid 1 1 stages = true)
    (f : Nat → Option Int) (cover : ∀ x, Outside (Flat 1 stages) f x) :
    ∀ n ∈ Flat 1 stages, f n ≠ none := by
  have seed : Rigid [] 1 := by
    intro _ v h
    refine ⟨fun _ h => by simp at h,?_⟩
    rcases h 0 with ⟨_,hn,_⟩|⟨t,ht,_⟩
    · simp at hn
    · simp [ht]
  simpa using chain (by decide : 0<1) (pre := []) (by simp) seed h f (by simpa using cover)

#print axioms essential
end PacketEssential
