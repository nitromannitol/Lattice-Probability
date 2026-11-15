import LatticeProb.Prob.MeasurableMarkedPhase
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap

/-! Markov kernels for marked coordinatewise phases. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace LatticeProb

/-- Sample coordinates from a fixed law and retain the mark after taking phases. -/
noncomputable def markedPhaseKernel {E ι : Type*} [MeasurableSpace E]
    (ν : Measure (ι → ℝ)) (a : ℝ) (θ : E → (ι → ℝ)) :
    Kernel E (E × (ι → ℝ)) :=
  (Kernel.id ×ₖ Kernel.const E ν).map
    (fun p => (p.1, fun i => Int.fract (a * p.2 i - θ p.1 i)))

/-- The kernel at a mark is the image of the coordinate law under its phase map. -/
theorem markedPhaseKernel_apply {E ι : Type*} [MeasurableSpace E]
    (ν : Measure (ι → ℝ)) [SFinite ν] (a : ℝ) (θ : E → (ι → ℝ))
    (hθ : Measurable θ) (e : E) :
    markedPhaseKernel ν a θ e =
      ν.map (fun x => (e, fun i => Int.fract (a * x i - θ e i))) := by
  have hf : Measurable (fun p : E × (ι → ℝ) =>
      (p.1, fun i => Int.fract (a * p.2 i - θ p.1 i))) := by
    exact (measurable_markedPhase θ hθ).comp ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  rw [markedPhaseKernel, Kernel.map_apply _ hf, Kernel.prod_apply,
    Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map hf measurable_prodMk_left]
  rfl

/-- A probability coordinate law gives a Markov kernel. -/
theorem markedPhaseKernel_isMarkovKernel {E ι : Type*} [MeasurableSpace E]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (a : ℝ)
    (θ : E → (ι → ℝ)) (hθ : Measurable θ) :
    IsMarkovKernel (markedPhaseKernel ν a θ) := by
  apply Kernel.IsMarkovKernel.map
  exact (measurable_markedPhase θ hθ).comp
    ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)

end LatticeProb
