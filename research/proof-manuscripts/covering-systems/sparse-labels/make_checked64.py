"""Generate the finite arithmetic data for the Lean proof from the CRT constructor."""
from pathlib import Path
from math import gcd
from examples import divisors,witness
def bez(l,n):
    u=pow(l,-1,n)
    return u,(1-l*u)//n

out=['''import IndexedDecisions
import Chain
import FinitePackets
namespace Checked64
open IntegerSubstitution CoveringResidues CoveringChain
set_option maxHeartbeats 0
set_option maxRecDepth 200000
local instance (m a b : Int) : Decidable (Same m a b) :=
  inferInstanceAs (Decidable (m ∣ a-b))

private theorem completeOption {n : Nat} (i : Option (Fin n)) :
    i ∈ none :: (List.finRange n).map some := by
  cases i with
  | none => simp
  | some j => simp [List.mem_finRange]

def m0 : Empty → Int := fun _ => 1
abbrev K0 := Empty
theorem core0 := @CoveringChain.seed
'''.replace('theorem core0 := @CoveringChain.seed','theorem core0 (ko : Empty → Prop) (u : Prop) : Old m0 1 ko u ↔ (∀ j,ko j) ∧ u := CoveringChain.seed ko u')]
prev=1
def arr(values):return '#['+', '.join(map(str,values))+']'
for i,(p,a) in enumerate([(2,3),(3,2),(11,1),(13,1)],1):
    bvals=[];evals=[];res=[]
    for j in range(1,a+1):
        for t,e in enumerate(divisors(prev)[:p-1],1):
            bvals.append(p**j);evals.append(e);res.append(t*p**(j-1))
    h=len(bvals);n=p**a;u,v=bez(prev,n)
    out.append(f'''
abbrev J{i} := Fin {h}
abbrev K{i} := Sum K{i-1} J{i}
def e{i} (i : Option J{i}) : Int := i.elim {prev} (fun j => {arr(evals)}[j.val]!)
def b{i} (i : Option J{i}) : Nat := i.elim {n} (fun j => {arr(bvals)}[j.val]!)
def r{i} (i : Option J{i}) : Int := i.elim 0 (fun j => {arr(res)}[j.val]!)
def m{i} : K{i} → Int := Sum.elim m{i-1} (fun j => e{i} (some j)*b{i} (some j))
theorem inner{i} (use : Option J{i} → Prop) : Covers (fun j => (b{i} j : Int)) use ↔ ∀ j,use j :=
  FinitePackets.minimal (none :: (List.finRange {h}).map some) completeOption (P:={n}) (by decide)
    b{i} r{i} (by decide) (by decide) (by decide) (by decide) use
theorem core{i} (ko : K{i} → Prop) (u : Prop) :
    Old m{i} {prev*n} ko u ↔ (∀ j,ko j) ∧ u := by
  apply stage m{i-1} e{i} (fun j => (b{i} j : Int))
  exact IntegerSubstitution.irreducible m{i-1} {prev} e{i} (fun j => (b{i} j : Int)) {prev} {n} {u} ({v})
    (by decide) (by decide) (by decide) (by decide)
    (lcmOfLast {prev} e{i} rfl (by decide)) core{i-1} inner{i}
''')
    prev*=n
ds=divisors(prev)[:35]
u,v=bez(prev,35)
out.append(f'''
def e5 (i : Fin 35) : Int := {arr(ds)}[i.val]!
theorem lastLcm (z : Int) : (∀ i, e5 i ∣ z) ↔ {prev} ∣ z := by
  constructor
  · intro h''')
for d in [8,9,11,13]:
    out.append(f'    have h{d} : ({d}:Int) ∣ z := h ⟨{ds.index(d)},by decide⟩')
out.append(f'''    omega
  · intro h i
    have all : ∀ i, e5 i ∣ {prev} := by decide
    exact Int.dvd_trans (all i) h
theorem finalPacket (use : Fin 35 → Prop) :
    Covers (fun _ : Fin 35 => 35) use ↔ ∀ j,use j :=
  FinitePackets.minimal (List.finRange 35) List.mem_finRange (P:=35) (by decide)
    (fun _ => 35) (fun i => (i.val:Int)) (by decide) (by decide) (by decide) (by decide) use
theorem everyDeletion (ko : K4 → Prop) (kn : Fin 35 → Prop) :
    New m4 e5 (fun _ => 35) ko kn ↔ (∀ j,ko j) ∧ (∀ i,kn i) :=
  IntegerSubstitution.irreducible m4 {prev} e5 (fun _ => 35) {prev} 35 {u} ({v}) (by decide)
    (by decide) (by decide) (by decide) lastLcm core4 finalPacket ko kn
abbrev Index64 := Sum K4 (Fin 35)
def m64 : Index64 → Int := Sum.elim m4 (fun j => e5 j*35)
def all0 : List K0 := []
''')
for i in range(1,5):
    out.append(f'def all{i} : List K{i} := all{i-1}.map Sum.inl ++ (List.finRange _).map Sum.inr')
out.append('''def indices : List Index64 := all4.map Sum.inl ++ (List.finRange _).map Sum.inr
def moduli : List Int := indices.map m64
theorem sizeAndMax : moduli.length=64 ∧ moduli.Nodup ∧ moduli.max? = some 13860 := by decide
#print axioms everyDeletion
#print axioms sizeAndMax
end Checked64''')
Path('Checked64.lean').write_text('\n'.join(out)+'\n')
