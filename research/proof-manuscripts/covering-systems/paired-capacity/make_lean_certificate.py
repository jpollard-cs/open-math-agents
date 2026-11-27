"""Regenerate the finite Lean example, including every modulus of every packet."""
from pathlib import Path
from carried_powers import construct
from plateau import build
import sys

is_zero = "--zero" in sys.argv
rows, stages = build(6313) if is_zero else construct(251,export=True)
cap = 66563 if is_zero else 63252
assert len(rows)==6313 and max(rows)==cap
name = "Zero6313" if is_zero else "Packet6313"
root = Path(__file__).resolve().parent
defs = ['import PacketAssignment', f'namespace {name}', 'open PacketCoverage',
        'set_option maxRecDepth 500000', 'set_option maxHeartbeats 0',
        'def multiples (b count : Nat) := (List.range count).map (fun i => b*(i+1))']
for i,stage in enumerate(stages):
    fixed=stage['fixed']
    if stage['carried'] is None:
        packet=fixed
    else:
        packet=[stage['carried'],*fixed]
    body=str(packet)
    # Encode long runs as a range rather than a gigantic list literal.
    for offset in [1,0]:
        seq=packet[offset:]
        if len(seq)<5:
            continue
        b=seq[0]
        run=0
        while run<len(seq) and seq[run]==b*(run+1):
            run+=1
        if run>=len(seq)-2:
            body=(f'{packet[0]} :: (' if offset else '(')+f'multiples {b} {run} ++ {seq[run:]})'
            break
    defs.append(f'def stage{i} : List Nat := {body}')
names=', '.join(f'stage{i}' for i in range(len(stages)))
defs += [f'def packets := [{names}]',
         'theorem valid : Valid 1 packets = true := by decide +kernel',
         'theorem every_integer (x : Int) : Hit 1 packets x := coverage valid (Int.one_dvd x)',
         'def entries := PacketEssential.Flat 1 packets',
         'theorem size : entries.length = 6313 := by decide +kernel',
         f'theorem maximum : entries.max? = some {cap} := by decide +kernel',
         'theorem distinct : entries.Nodup := (unused_sound (seen := 0) (by decide +kernel)).1',
         'def trialPrime (p : Nat) : Bool := p ≥ 2 && (List.range (p-2)).all (fun i => p % (i+2) != 0)',
         'def budget (cap : Nat) := 1 + ((List.range 258).filter trialPrime).foldl (fun s p =>',
         '  s + ((List.range 17).filter (fun j => p^(j+1)*(p+1) ≤ cap)).length*(p-1)) 0',
         'theorem budgets : budget 63252 = 6283 ∧ budget 66305 = 6283 ∧ budget 66306 = 6539 := by decide +kernel',
         'theorem fibre_certificate : PacketEssential.StrictValid 1 1 packets = true := by decide +kernel',
         'theorem all_reassignments (f : Nat → Option Int) (h : ∀ x, PacketEssential.Outside entries f x) :',
         '    ∀ n ∈ entries, f n ≠ none := PacketEssential.essential fibre_certificate f h',
         'theorem after_deletion (n : Nat) (hn : n ∈ entries) (a : Nat → Int) :',
         '    ∃ x : Int, ∀ m ∈ entries, m ≠ n → ¬ (m : Int) ∣ x - a m := by',
         '  classical', '  apply Classical.byContradiction', '  intro h',
         '  let f := fun m => if m=n then none else some (a m)',
         '  have cover (x : Int) : PacketEssential.Outside entries f x := by',
         '    apply Classical.byContradiction','    intro missing',
         '    apply h ⟨x,?_⟩', '    intro m hm he hd',
         '    exact missing ⟨m,hm,a m,by simp [f,he],hd⟩',
         '  exact all_reassignments f cover n hn (by simp [f])',
         'theorem covering : ∃ a : Nat → Int, ∀ x : Int, ∃ n ∈ entries, (n : Int) ∣ x-a n :=',
         '  PacketAssignment.covers valid distinct',
         'theorem nontrivial : ∀ n ∈ entries, 1 < n := by',
         '  have h : entries.all (fun n => 1 < n) = true := by decide +kernel',
         '  exact fun n hn => of_decide_eq_true (List.all_eq_true.mp h n hn)',
         '#print axioms covering', '#print axioms nontrivial', '#print axioms after_deletion', '#print axioms every_integer', '#print axioms size', '#print axioms maximum',
         '#print axioms distinct', '#print axioms budgets', f'end {name}']
if is_zero:
    defs[-1:-1] = [
      'def actualPeriod := entries.foldl Nat.lcm 1',
      'def defectBaseline := 1 + ((List.range 258).filter trialPrime).foldl (fun s p =>',
      '  s + ((List.range 17).filter (fun j => actualPeriod % (p^(j+1)) == 0)).length*(p-1)) 0',
      'theorem period_data : actualPeriod = '+str(__import__('math').lcm(*rows))+' := by decide +kernel',
      'theorem zero_count : defectBaseline = entries.length := by decide +kernel',
      'theorem plateau_budget : budget 66562 = 6539 := by decide +kernel',
      '#print axioms zero_count','#print axioms plateau_budget']
(root/(name+'.lean')).write_text('\n'.join(defs)+'\n')
