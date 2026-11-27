import PrimeBlockMesh
import ReciprocalBandRates

/-! Exact certificates for the 31 lower bands in the 48-band prime sieve.
The level exponent is the reciprocal of the target coefficient, diminished
by one billionth. Its loss fits strictly within each stated allowance. -/

noncomputable section
open Finset
namespace FactorialLowerBands
open PrimeBlockMesh

def ampPower (j : ℕ) : ℝ := if j<16 then 1/15 else 1/7
def endpointPower (j : ℕ) : ℝ := if j<16 then 2/3 else 3/7
def modulusPower (j : ℕ) : ℝ := if j<16 then 11/15 else 4/7

/-- The unperturbed reciprocal coefficient follows from the indicated
exponent pair. Both formulas are rational at the mesh endpoints. -/
def levelPower (j : ℕ) : ℝ :=
  (if j<16 then 17/24-(5/4)*(edge (j+1):ℝ) else 19/54-(edge (j+1):ℝ)/2) - 1/1000000000

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 12000 in
/-- All size requirements, three strict power savings, and the allowance
comparison for each of the first 31 mesh intervals. -/
theorem lower_band_parameters (j : ℕ) (hj : j<31) :
    let a := (edge j:ℝ)
    let b := (edge (j+1):ℝ)
    let g := levelPower j
    let p := ampPower j
    let q := endpointPower j
    let s := modulusPower j
    0<g ∧ g≤1 ∧ 0≤a ∧ a≤b ∧ b≤1 ∧ 0≤p ∧ p≤1 ∧ 0≤q ∧ s<1 ∧
      2*g<a ∧ p+b*q+g*(2*(1-s))<ReciprocalBandRates.c ∧
      2*b-1<ReciprocalBandRates.c ∧ (b-a)/g < (allowance j:ℝ) := by
  interval_cases j <;>
    norm_num [levelPower,ampPower,endpointPower,modulusPower,edge,allowance,ReciprocalBandRates.c]

end FactorialLowerBands
#print axioms FactorialLowerBands.lower_band_parameters
