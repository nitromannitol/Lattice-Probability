/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianStoppingLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianFiniteStopping
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Passing actual stopped Brownian laws through a continuous time limit

Dominated convergence for bounded continuous tests identifies the limiting
measure. The application to dyadic stopping times uses the actual stationary
shift law already proved at each finite approximation.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace BouRabeeGwynne

lemma continuous_shiftedBrownianPath {d : ℕ} :
    Continuous (fun p : ℝ≥0 × BrownianPath d ↦ shiftedBrownianPath p.1 p.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (ℝ≥0 × BrownianPath d) × ℝ≥0 ↦
    p.1.2 (p.1.1 + p.2) - p.1.2 p.1.1)
  fun_prop

lemma map_eq_of_ae_tendsto_of_map_eq {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {P : Measure Ω} [IsFiniteMeasure P]
    {f : Ω → BrownianPath d} {fₙ : ℕ → Ω → BrownianPath d}
    (hf : Measurable f) (hfₙ : ∀ n, Measurable (fₙ n))
    {ν : Measure (BrownianPath d)} (heq : ∀ n, P.map (fₙ n) = ν)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ fₙ n ω) atTop (𝓝 (f ω))) :
    P.map f = ν := by
  haveI : IsFiniteMeasure ν := by rw [← heq 0]; infer_instance
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  have hint := tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ ‖g‖)
    (fun n ↦ (g.continuous.measurable.comp (hfₙ n)).aestronglyMeasurable)
    (integrable_const _)
    (fun n ↦ Filter.Eventually.of_forall fun ω ↦ g.norm_coe_le_norm _)
    (hlim.mono fun ω hω ↦ g.continuous.continuousAt.tendsto.comp hω)
  have hconst : Tendsto (fun n ↦ ∫ ω, g (fₙ n ω) ∂P)
      atTop (𝓝 (∫ x, g x ∂ν)) := by
    have hval (n : ℕ) : (∫ ω, g (fₙ n ω) ∂P) = ∫ x, g x ∂ν := by
      rw [← integral_map (hfₙ n).aemeasurable g.continuous.measurable.aestronglyMeasurable,
        heq n]
    simpa only [hval] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ ∫ x, g x ∂ν) atTop (𝓝 _))
  rw [integral_map hf.aemeasurable g.continuous.measurable.aestronglyMeasurable]
  exact tendsto_nhds_unique hint hconst

end BouRabeeGwynne
