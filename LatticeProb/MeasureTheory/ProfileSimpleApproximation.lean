import LatticeProb.MeasureTheory.ProfileConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDense

/-! # Simple approximations of measurable profiles -/

set_option autoImplicit false

open Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace LatticeProb.MeasurableProfile

variable {α E : Type*} [MeasurableSpace α] [PseudoEMetricSpace E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [SecondCountableTopology E]
  (μ : Measure α) [IsFiniteMeasure μ] [Nonempty E]

/-- Every almost-everywhere measurable profile is a limit of simple profiles. -/
theorem exists_simple_tendsto (f : MeasurableProfile (E := E) μ) :
    ∃ s : ℕ → SimpleFunc α E,
      Tendsto (fun n => (⟨s n, (s n).measurable.aemeasurable⟩ :
        MeasurableProfile (E := E) μ)) atTop (@nhds (MeasurableProfile (E := E) μ)
          (instPseudoMetricSpace μ).toUniformSpace.toTopologicalSpace f) := by
  classical
  let g := f.2.mk f.1
  have hg : Measurable g := f.2.measurable_mk
  let y : E := Classical.choice ‹Nonempty E›
  let s : ℕ → SimpleFunc α E := fun n =>
    SimpleFunc.approxOn g hg Set.univ y (Set.mem_univ y) n
  refine ⟨s, (tendsto_iff_tendstoInMeasure μ _ f).2 ?_⟩
  apply TendstoInMeasure.congr_right f.2.ae_eq_mk.symm
  apply tendstoInMeasure_of_tendsto_ae_of_measurable_edist
  · intro n
    exact (s n).measurable.edist hg
  · filter_upwards with x
    exact SimpleFunc.tendsto_approxOn hg (Set.mem_univ y) (by simp)

end LatticeProb.MeasurableProfile
