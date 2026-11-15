import LatticeProb.Bonanno.ReflectedGMS.Limit.PathLawFiniteDimensionalConvergence
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! # Uniqueness of limits of finite-coordinate tests -/

set_option autoImplicit false

open Filter MeasureTheory
open scoped BoundedContinuousFunction Topology

namespace LatticeProb

/-- Two finite continuous-path laws agree when every bounded continuous
finite-coordinate test has the same approximating net for both laws. -/
theorem continuousPath_measure_eq_of_common_finite_test_limits
    {X E ι : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [LocallyCompactSpace X] [MetricSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] {l : Filter ι} [l.NeBot]
    {μ ν : Measure C(X, E)} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A : ∀ I : Finset X, ((I → E) →ᵇ ℝ) → ι → ℝ)
    (hμ : ∀ (I : Finset X) (g : (I → E) →ᵇ ℝ),
      Tendsto (A I g) l (𝓝 (∫ f, g (I.restrict (fun x => f x)) ∂μ)))
    (hν : ∀ (I : Finset X) (g : (I → E) →ᵇ ℝ),
      Tendsto (A I g) l (𝓝 (∫ f, g (I.restrict (fun x => f x)) ∂ν))) :
    μ = ν := by
  apply ReflectedGMS.MartingaleLimit.measure_eq_of_forall_map_finsetRestrict_eq
  intro I
  let r : C(X, E) → I → E := fun f => I.restrict (fun x => f x)
  have hr : Measurable r :=
    (ReflectedGMS.MartingaleLimit.continuous_finsetRestrict_pathCoordinates I).measurable
  change μ.map r = ν.map r
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [integral_map hr.aemeasurable g.continuous.aestronglyMeasurable,
    integral_map hr.aemeasurable g.continuous.aestronglyMeasurable]
  exact tendsto_nhds_unique (hμ I g) (hν I g)

end LatticeProb
