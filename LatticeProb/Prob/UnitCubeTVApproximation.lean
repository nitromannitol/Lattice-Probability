import LatticeProb.Prob.MarkPreservingKernel
import LatticeProb.Prob.MapKernelTVApproximation
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Approximation of a measurable image by independent uniform coordinates. -/

open MeasureTheory ProbabilityTheory Set

namespace LatticeProb

/-- Lebesgue measure restricted to the half-open unit cube. -/
noncomputable def unitCubeMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  volume.restrict (Set.univ.pi fun _ => Ico (0 : ℝ) 1)

instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (unitCubeMeasure ι) := by
  have : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) := by
    constructor
    simp [Real.volume_Ico]
  unfold unitCubeMeasure
  rw [volume_pi, Measure.restrict_pi_pi]
  infer_instance

/-- Total variation comparison with an independent uniform cube is stable
under approximation of the underlying finite measure. -/
theorem tvDist_map_prod_unitCube_le_of_approx {E X ι : Type*}
    [MeasurableSpace E] [MeasurableSpace X] [Fintype ι]
    (μ ν : Measure (E × X)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {g : E × X → E × (ι → ℝ)} (hg : Measurable g) :
    QuantumZipper.TV.tvDist (μ.map g) ((μ.map Prod.fst).prod (unitCubeMeasure ι)) ≤
      QuantumZipper.TV.tvDist (ν.map g) ((ν.map Prod.fst).prod (unitCubeMeasure ι)) +
        (QuantumZipper.TV.tvDist μ ν + QuantumZipper.TV.tvDist μ ν) := by
  let κ := markResamplingKernel (Prod.fst : E × X → E) measurable_fst (unitCubeMeasure ι)
  have h := tvDist_map_comp_le_of_approx μ ν hg κ
  simpa only [κ, markResamplingKernel_comp] using h

end LatticeProb
