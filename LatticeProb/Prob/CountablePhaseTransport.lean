import LatticeProb.Prob.CountableUniformPhaseKernel
import LatticeProb.Prob.AbsolutelyContinuousPhase
import Mathlib.Probability.Kernel.Composition.CompMap

/-! Transport of fixed-dimensional phase laws to a countable disjoint union. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LatticeProb

private theorem measurable_phase_inject {E : Type*} [MeasurableSpace E] (n : ℕ) :
    Measurable (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n) := by
  intro s hs
  change MeasurableSet[⨅ i : ℕ, (inferInstance : MeasurableSpace (E × (Fin i → ℝ))).map
    (Sigma.mk i)] s at hs
  exact (MeasurableSpace.measurableSet_iInf.mp hs) n

/-- Resampling on an embedded count fiber uses that fiber's own mark marginal. -/
theorem countableUniformPhaseKernel_comp_map {E : Type*} [MeasurableSpace E]
    (n : ℕ) (μ : Measure (E × (Fin n → ℝ))) [SFinite μ] :
    countableUniformPhaseKernel ∘ₘ (μ.map (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n)) =
      ((μ.map Prod.fst).prod (unitCubeMeasure (Fin n))).map
        (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n) := by
  let j := @Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n
  have hj : Measurable j := measurable_phase_inject n
  let κ := markResamplingKernel (Prod.fst : E × (Fin n → ℝ) → E) measurable_fst
    (unitCubeMeasure (Fin n))
  have hk : countableUniformPhaseKernel ∘ₖ Kernel.deterministic j hj = κ.map j := by
    ext p s hs
    rw [Kernel.comp_deterministic_eq_comap _ hj, Kernel.comap_apply _ hj, Kernel.map_apply _ hj]
    exact congrArg (fun m : Measure (CountablePhaseSpace E) => m s)
      (countableUniformPhaseKernel_apply n p)
  rw [← Measure.deterministic_comp_eq_map hj, Measure.comp_assoc, hk,
    ← Measure.map_comp μ κ hj, markResamplingKernel_comp]

/-- Phase maps commute with embedding a fixed coordinate count. -/
theorem countablePhaseMap_map {E : Type*} [MeasurableSpace E]
    (n : ℕ) (μ : Measure (E × (Fin n → ℝ))) (a : ℝ)
    (θ : ∀ k, E → (Fin k → ℝ)) (hθ : ∀ k, Measurable (θ k)) :
    (μ.map (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n)).map
        (countablePhaseMap a θ) =
      (μ.map (fun x => (x.1, fun i => Int.fract (a * x.2 i - θ n x.1 i)))).map
        (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n) := by
  have hj := measurable_phase_inject (E := E) n
  have hp : Measurable (fun x : E × (Fin n → ℝ) =>
      (x.1, fun i => Int.fract (a * x.2 i - θ n x.1 i))) := by
    refine measurable_fst.prodMk (Measurable.of_eval fun i => ?_)
    exact measurable_fract.comp ((measurable_const.mul ((measurable_pi_apply i).comp measurable_snd)).sub
      ((measurable_pi_apply i).comp ((hθ n).comp measurable_fst)))
  rw [Measure.map_map (measurable_countablePhaseMap a θ hθ) hj, Measure.map_map hj hp]
  rfl

end LatticeProb
