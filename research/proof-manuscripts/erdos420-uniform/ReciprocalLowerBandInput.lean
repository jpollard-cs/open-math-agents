import ReciprocalUpperBands

noncomputable section
open Real
namespace FactorialLowerBands

/-- A full-band Selberg bound after summing scale-dependent local sieves. -/
def BandBound (p q s : ℝ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (n h z : ℕ) (u v : ℝ), 0<n → 1≤z → (z:ℝ)^2≤u → u≤v →
    FactorialUpperBands.primeHits n h u v ≤
      (h:ℝ)*log (v/u)/log ((z:ℝ)+1) + 4*h*(z:ℝ)^2/u +
      C*(1+log (v/u)/log 2)*((n:ℝ)+h)^p*v^q*(z:ℝ)^(2*(1-s)) +
      C*(v^2/(n:ℝ))*(1+log z)^3

end FactorialLowerBands
