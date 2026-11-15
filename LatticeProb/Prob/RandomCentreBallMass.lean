import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-! # Small-ball mass at a random centre -/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped ENNReal

namespace LatticeProb

/-- A finite net reduces a small-mass event at an arbitrary random centre to
fixed-centre events. No independence or measurability of the centre is needed. -/
theorem measure_randomCentre_ball_mass_le_sum
    {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [PseudoMetricSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (z : Ω → X) (A : Set X)
    (s : Finset ι) (c : ι → X) (r : ℝ) (t : ℝ≥0∞)
    (hcover : ∀ x ∈ A, ∃ i ∈ s, dist (c i) x < r) :
    P {ω | z ω ∈ A ∧ μ ω (ball (z ω) (2 * r)) ≤ t} ≤
      ∑ i ∈ s, P {ω | μ ω (ball (c i) r) ≤ t} := by
  have hsub : {ω | z ω ∈ A ∧ μ ω (ball (z ω) (2 * r)) ≤ t} ⊆
      ⋃ i ∈ s, {ω | μ ω (ball (c i) r) ≤ t} := by
    intro ω hω
    obtain ⟨i, hi, hd⟩ := hcover (z ω) hω.1
    refine mem_iUnion.2 ⟨i, mem_iUnion.2 ⟨hi, ?_⟩⟩
    exact (measure_mono (ball_subset_ball' (by linarith [hd.le]))).trans hω.2
  exact (measure_mono hsub).trans (measure_biUnion_finset_le s _)

/-- A uniform fixed-centre lower-tail estimate costs at most the size of the net. -/
theorem measure_randomCentre_ball_mass_le_card_mul
    {Ω X ι : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [PseudoMetricSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (z : Ω → X) (A : Set X)
    (s : Finset ι) (c : ι → X) (r : ℝ) (t p : ℝ≥0∞)
    (hcover : ∀ x ∈ A, ∃ i ∈ s, dist (c i) x < r)
    (htail : ∀ i ∈ s, P {ω | μ ω (ball (c i) r) ≤ t} ≤ p) :
    P {ω | z ω ∈ A ∧ μ ω (ball (z ω) (2 * r)) ≤ t} ≤ s.card * p := by
  calc
    _ ≤ ∑ i ∈ s, P {ω | μ ω (ball (c i) r) ≤ t} :=
      measure_randomCentre_ball_mass_le_sum P μ z A s c r t hcover
    _ ≤ ∑ _i ∈ s, p := Finset.sum_le_sum htail
    _ = s.card * p := by rw [Finset.sum_const, nsmul_eq_mul]

end LatticeProb
