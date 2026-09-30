/-
Continuity of the integration functional on continuous test functions over a compact space,
and the resulting full-measure event making a countable family of weighted integral identities
hold simultaneously for every continuous test coefficient.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.SimultaneousTesting
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

open MeasureTheory TopologicalSpace
noncomputable section
namespace LatticeProb.Scaling.SimultaneousTesting

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ]

/-- Integration against a fixed finite measure is continuous on the continuous functions of a
compact space, in the sup norm. -/
theorem continuous_integral_continuousMap :
    Continuous (fun f : C(X, ℝ) => ∫ x, f x ∂μ) := by
  have hc := continuous_integral.comp (ContinuousMap.toLp (E := ℝ) 1 μ ℝ).continuous
  exact hc.congr fun f => integral_congr_ae (ContinuousMap.coeFn_toLp μ f)

/-- A family of continuous test coefficients on a compact space admits one
full-measure event for all its weighted integral identities. -/
theorem ae_forall_integral_mul_eq_zero
    [SecondCountableTopology X] [T2Space X]
    {Ω T : Type*} [MeasurableSpace Ω] {Q : Measure Ω}
    (u : Ω → C(X, ℝ)) (J : T → C(X, ℝ)) {A : Ω → Prop}
    (heq : ∀ t, ∀ᵐ ω ∂Q, A ω → (∫ x, u ω x * J t x ∂μ) = 0) :
    ∀ᵐ ω ∂Q, A ω → ∀ t, (∫ x, u ω x * J t x ∂μ) = 0 := by
  letI : TopologicalSpace T := TopologicalSpace.induced J inferInstance
  letI : SecondCountableTopology T := secondCountableTopology_induced T C(X, ℝ) J
  have hJ : Continuous J := continuous_induced_dom
  apply ae_forall_eq_of_continuous (f := fun ω t => ∫ x, u ω x * J t x ∂μ)
    (g := fun _ _ => (0 : ℝ))
  · exact Filter.Eventually.of_forall fun ω _ =>
      continuous_integral_continuousMap.comp (continuous_const.mul hJ)
  · exact Filter.Eventually.of_forall fun _ _ => continuous_const
  · exact heq
end LatticeProb.Scaling.SimultaneousTesting
