import PacketAssignment
import StarCoordinates

namespace Integer29
open PacketEssential
open ForestFibre

def bin : List Nat := [16,8,4,2]
def d3 : List Nat := [1,2,4]
def d5 : List Nat := [1,2,4,8,16]
def mods (b : Nat) (ds : List Nat) := ds.map (b*·)
def pre := bin ++ (mods 5 d3 ++ (mods 7 d5 ++ (mods 15 d3 ++ mods 21 d3)))
def finish : List (List Nat) := [[176,11,22,33,44,55,66,77,88,110,132]]
def allMods := Flat 1680 finish ++ pre

private theorem base : Rigid bin 16 := by
  have start : Rigid [] 1 := by
    intro f v h
    refine ⟨by simp,?_⟩
    rcases h 0 with ⟨_,hn,_⟩|⟨r,hr,_⟩
    · simp at hn
    · simp [hr]
  have b2 := rigid_step (L:=1) (d:=1) (ns:=[2]) (c:=2) (by decide)
    (by simp) start (by decide) (by decide)
  have b4 := rigid_step (L:=2) (ns:=[4]) (c:=4) (by decide) (by decide)
    b2 (by decide) (by decide)
  have b8 := rigid_step (L:=4) (ns:=[8]) (c:=8) (by decide) (by decide)
    b4 (by decide) (by decide)
  exact rigid_step (L:=8) (ns:=[16]) (c:=16) (by decide) (by decide)
    b8 (by decide) (by decide)

def digit (p : Nat) (x : Int) := (x % (p:Int)).toNat
def active {T : Type} (b : Nat) (ds : List Nat) (f : Nat → Option Int) (x : Int)
    (label : Int → T) : List T := ds.filterMap (fun d => do
      let r ← f (b*d)
      if (d:Int) ∣ x-r then some (label r) else none)

private theorem mod_same {a b : Int} {s : Nat} (h : (s:Int) ∣ a-b) : digit s a=digit s b := by
  exact congrArg Int.toNat (Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd h))

private theorem project {T : Type} {b : Nat} {ds : List Nat}
    (hds : ∀ d∈ds, d∣16) {x z : Int} (hx : (16:Int)∣z-x)
    (label : Int → T) (respect : ∀ r, (b:Int)∣z-r → label z=label r)
    {f : Nat → Option Int} (hit : Outside (mods b ds) f z) : label z∈active b ds f x label := by
  obtain ⟨n,hn,r,hr,hd⟩ := hit
  obtain ⟨d,hm,rfl⟩ := List.mem_map.mp hn
  have h1 : (d:Int) ∣ z-x := Int.dvd_trans (Int.ofNat_dvd.mpr (hds d hm)) hx
  have h2 : (d:Int) ∣ z-r := Int.dvd_trans (Int.dvd_mul_left ..) (by simpa using hd)
  have h3 : (d:Int) ∣ x-r := by
    have h := Int.dvd_sub h2 h1
    rwa [show z-r-(z-x)=x-r by omega] at h
  have h4 : (b:Int) ∣ z-r := Int.dvd_trans (Int.dvd_mul_right ..) (by simpa using hd)
  exact List.mem_filterMap.mpr ⟨d,hm,by simp [hr,h3,respect r h4]⟩

private theorem activeUsed {b : Nat} {ds : List Nat} {f : Nat → Option Int} {x : Int}
    {T : Type} {label : Int → T} (all : (active b ds f x label).length=ds.length) :
    ∀ n∈mods b ds, f n ≠ none := by
  intro n hn nf
  obtain ⟨d,hm,rfl⟩ := List.mem_map.mp hn
  have hlt : (active b ds f x label).length < ds.length := by
    apply List.length_filterMap_lt_length_iff_exists.mpr
    exact ⟨d,hm,by simp [nf]⟩
  omega

private theorem onBin {f : Nat→ Option Int} {x z : Int} (hx : (16:Int) ∣ z-x)
    (h : Outside bin f z) : Outside bin f x := by
  obtain ⟨n,hn,r,hr,hd⟩ := h
  have hn16 : n∣16 := (by decide : ∀ n∈bin, n∣16) n hn
  have hh := Int.dvd_sub hd (Int.dvd_trans (Int.ofNat_dvd.mpr hn16) hx)
  exact ⟨n,hn,r,hr,by simpa [show z-r-(z-x)=x-r by omega] using hh⟩

private theorem fibre {f : Nat → Option Int} {v : Option Int}
    (cover : ∀ s, Outside pre f s ∨ Has 1680 v s)
    {x : Int} (hole : ¬Outside bin f x) :
    Has 16 v x ∧ ∀ n∈(mods 5 d3 ++ (mods 7 d5 ++ (mods 15 d3 ++ mods 21 d3))), f n ≠ none := by
  let pair := fun (p : Nat) (r : Int) => (digit 3 r, digit p r)
  let u5 := active 5 d3 f x (digit 5)
  let u7 := active 7 d5 f x (digit 7)
  let e5 := active 15 d3 f x (pair 5)
  let e7 := active 21 d3 f x (pair 7)
  have h5 : u5.length≤3 := List.length_filterMap_le .. 
  have h7 : u7.length≤5 := List.length_filterMap_le ..
  have f5 : e5.length≤3 := List.length_filterMap_le ..
  have f7 : e7.length≤3 := List.length_filterMap_le ..
  have legal := StarCoordinates.compulsory u5 u7 e5 e7 h5 h7 f5 f7 (Has 16 v x)
    (digit 3 (v.getD 0)) (digit 5 (v.getD 0)) (digit 7 (v.getD 0)) (by
      intro i hi j hj k hk hu5 hu7 he5 he7
      let s : Int := 945*x+1120*i+336*j+960*k
      have sx : (16:Int)∣s-x := by dsimp [s]; omega
      have si : digit 3 s=i := by dsimp [s,digit]; omega
      have sj : digit 5 s=j := by dsimp [s,digit]; omega
      have sk : digit 7 s=k := by dsimp [s,digit]; omega
      rcases cover s with ⟨n,hn,hit⟩ | ⟨r,hr,hd⟩
      · simp only [pre, List.mem_append] at hn
        rcases hn with hb|h|h|h|h
        · exact False.elim (hole (onBin sx ⟨n,hb,hit⟩))
        · have out := project (b:=5) (ds:=d3) (by decide) sx (digit 5) (fun _ => mod_same) ⟨n,h,hit⟩
          exact False.elim (hu5 (sj ▸ out))
        · have out := project (b:=7) (ds:=d5) (by decide) sx (digit 7) (fun _ => mod_same) ⟨n,h,hit⟩
          exact False.elim (hu7 (sk ▸ out))
        · have out := project (b:=15) (ds:=d3) (by decide) sx (pair 5) (fun r h => by
            exact Prod.ext (mod_same (Int.dvd_trans (by decide : (3:Int)∣15) h))
              (mod_same (Int.dvd_trans (by decide : (5:Int)∣15) h))) ⟨n,h,hit⟩
          exact False.elim (he5 (by simpa [pair,si,sj] using out))
        · have out := project (b:=21) (ds:=d3) (by decide) sx (pair 7) (fun r h => by
            exact Prod.ext (mod_same (Int.dvd_trans (by decide : (3:Int)∣21) h))
              (mod_same (Int.dvd_trans (by decide : (7:Int)∣21) h))) ⟨n,h,hit⟩
          exact False.elim (he7 (by simpa [pair,si,sk] using out))
      · have qr : (16:Int)∣s-r := Int.dvd_trans (by decide : (16:Int)∣1680) hd
        have hxr := Int.dvd_sub qr sx
        have m3 := mod_same (Int.dvd_trans (by decide : (3:Int)∣1680) hd)
        have m5 := mod_same (Int.dvd_trans (by decide : (5:Int)∣1680) hd)
        have m7 := mod_same (Int.dvd_trans (by decide : (7:Int)∣1680) hd)
        refine ⟨⟨r,hr,by simpa [show s-r-(s-x)=x-r by omega] using hxr⟩,?_,?_,?_⟩
        · simpa [hr,si] using m3
        · simpa [hr,sj] using m5
        · simpa [hr,sk] using m7)
  refine ⟨legal.1,?_⟩
  intro n hn
  simp only [List.mem_append] at hn
  rcases hn with h|h|h|h
  · exact activeUsed legal.2.1 _ h
  · exact activeUsed legal.2.2.1 _ h
  · exact activeUsed legal.2.2.2.1 _ h
  · exact activeUsed legal.2.2.2.2 _ h

theorem before : Rigid pre 1680 := by
  intro f v cov
  have h : ∃ x, ¬Outside bin f x := by
    apply Classical.byContradiction
    intro no
    have all (x) : Outside bin f x := Classical.byContradiction (fun hn => no ⟨x,hn⟩)
    exact (base f none (fun x => Or.inl (all x))).2 rfl
  obtain ⟨x,hx⟩ := h
  have here := fibre cov hx
  have bc := base f v (fun z => by
    by_cases ok : Outside bin f z
    · exact Or.inl ok
    · exact Or.inr (fibre cov ok).1)
  refine ⟨?_,bc.2⟩
  intro n hn
  rcases List.mem_append.mp hn with hb|ho
  · exact bc.1 n hb
  · exact here.2 n ho

theorem after_deletion (f : Nat → Option Int) (cover : ∀ x : Int, Outside allMods f x) :
    ∀ n∈allMods, f n ≠ none :=
  chain (L:=1680) (pre:=pre) (stages:=finish) (by decide) (by decide) before (by decide) f cover

#print axioms before
#print axioms after_deletion


def phases : List (Nat × Int) := [(2,1), (4,2), (5,2), (7,2), (8,4), (10,8), (11,0), (14,10), (15,10), (16,8), (20,4), (21,14), (22,8), (28,4), (30,16), (33,27), (42,8), (44,24), (55,10), (56,40), (60,36), (66,18), (77,70), (84,36), (88,56), (110,20), (112,48), (132,72), (176,80)]

set_option maxRecDepth 200000
set_option maxHeartbeats 0

def finiteHit (x : Nat) : Bool :=
  phases.any (fun e => decide ((e.1:Int) ∣ (x:Int)-e.2))

-- Separate short intervals bound the reduction depth of the finite kernel check.
private theorem finite : ∀ t:Fin 116, ∀ i:Fin 160, finiteHit (t.val*160+i.val)=true := by decide

theorem every_integer (x : Int) : ∃ n∈allMods, (n:Int) ∣ x-PacketAssignment.residue phases n := by
  let y := (x%18480).toNat
  have non : 0≤x%18480 := Int.emod_nonneg _ (by decide)
  have lt : x%18480<18480 := Int.emod_lt_of_pos _ (by decide)
  have yi : (y:Int)=x%18480 := Int.toNat_of_nonneg non
  have yy : y<18480 := by omega
  have h := finite ⟨y/160,by omega⟩ ⟨y%160,by omega⟩
  have hv : finiteHit y = true := by
    have eql : y/160*160+y%160=y := by omega
    simpa only [eql] using h
  obtain ⟨e,mem,hd⟩ := List.any_eq_true.mp hv
  have nm : e.1∈allMods := (by decide : ∀ c∈phases, c.1∈allMods) e mem
  have su : e.1 ∣ 18480 := (by decide : ∀ n∈allMods, n∣18480) e.1 nm
  have h1 : (18480:Int) ∣ x-y := ⟨x/18480,by omega⟩
  have h2 := Int.dvd_trans (Int.ofNat_dvd.mpr su) h1
  have h3 := Int.dvd_add h2 (of_decide_eq_true hd)
  refine ⟨e.1,nm,?_⟩
  rw [PacketAssignment.agree (by decide : (phases.map Prod.fst).Nodup) mem]
  rwa [show x-(y:Int)+((y:Int)-e.2)=x-e.2 by omega] at h3

theorem covering : ∃ a : Nat → Int, ∀ x : Int, ∃ n∈allMods, (n:Int)∣x-a n :=
  ⟨PacketAssignment.residue phases,every_integer⟩
theorem size : allMods.length=29 := by decide
theorem distinct : allMods.Nodup := by decide
theorem maximum : 176∈allMods ∧ ∀ n∈allMods, 1<n ∧ n≤176 := by decide
#print axioms covering
#print axioms size
#print axioms distinct
#print axioms maximum
end Integer29
