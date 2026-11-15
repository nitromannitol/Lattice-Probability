import LatticeProb.Prob.FullDensityPhase
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

/-! Phase convergence for finite absolutely continuous measures. -/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- A finite measure absolutely continuous with respect to its mark marginal
and Lebesgue measure has asymptotically uniform coordinate phases. -/
theorem tendsto_tvDist_phase_of_absolutelyContinuous
    {E τ : Type*} [MeasurableSpace E] {l : Filter τ}
    (n : ℕ) (μ : Measure (E × (Fin n → ℝ))) [IsFiniteMeasure μ]
    (hμ : μ ≪ (μ.map Prod.fst).prod (volume : Measure (Fin n → ℝ)))
    (a : τ → ℝ) (ha : Tendsto a l atTop) (θ : τ → E → (Fin n → ℝ))
    (hθ : ∀ t, Measurable (θ t)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      (μ.map (fun x => (x.1, fun i => Int.fract (a t * x.2 i - θ t x.1 i))))
      ((μ.map Prod.fst).prod (unitCubeMeasure (Fin n)))) l (𝓝 0) := by
  let ρ := μ.map Prod.fst
  let ν := ρ.prod (volume : Measure (Fin n → ℝ))
  have hrep : ν.withDensity (μ.rnDeriv ν) = μ :=
    Measure.withDensity_rnDeriv_eq μ ν hμ
  let : IsFiniteMeasure (ν.withDensity (μ.rnDeriv ν)) := by rw [hrep]; infer_instance
  have h := tendsto_tvDist_density_phase ρ n (μ.rnDeriv ν)
    (Measure.measurable_rnDeriv μ ν) a ha θ hθ
  dsimp only [ν] at hrep h
  rw [hrep] at h
  exact h

end LatticeProb
