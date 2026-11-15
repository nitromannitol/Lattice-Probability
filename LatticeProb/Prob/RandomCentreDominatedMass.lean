import LatticeProb.Prob.RandomCentreBallMass

/-! # Small-ball tails under local measure domination -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

/-- A fixed-centre lower-tail bound for a locally dominated measure controls
small balls around an arbitrary, possibly dependent, random centre. -/
theorem measure_randomCentre_ball_mass_le_of_ae_domination
    {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [PseudoMetricSpace X]
    (P : Measure Ω) (μ ν : Ω → Measure X) (z : Ω → X) (A : Set X)
    (s : Finset ι) (c : ι → X) (r : ℝ) (t p : ℝ≥0∞)
    (hcover : ∀ x ∈ A, ∃ i ∈ s, dist (c i) x < r)
    (hdom : ∀ᵐ ω ∂P, ∀ i ∈ s, ν ω (ball (c i) r) ≤ μ ω (ball (c i) r))
    (htail : ∀ i ∈ s, P {ω | ν ω (ball (c i) r) ≤ t} ≤ p) :
    P {ω | z ω ∈ A ∧ μ ω (ball (z ω) (2 * r)) ≤ t} ≤ s.card * p := by
  apply measure_randomCentre_ball_mass_le_card_mul P μ z A s c r t p hcover
  intro i hi
  refine (measure_mono_ae ?_).trans (htail i hi)
  filter_upwards [hdom] with ω hω hevent
  exact (hω i hi).trans hevent

end LatticeProb
