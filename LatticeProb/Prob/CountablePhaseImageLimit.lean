import LatticeProb.Prob.CountablePhaseTotalLimit

/-! Total variation convergence under parameter-dependent measurable images. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- A common measurable image preserves total variation convergence, even when
    the image map varies with the parameter. -/
theorem tendsto_tvDist_map_of_tendsto
    {α β τ : Type*} [MeasurableSpace α] [MeasurableSpace β] {l : Filter τ}
    (μ ν : τ → Measure α) (f : τ → α → β) (hf : ∀ t, Measurable (f t))
    (h : Tendsto (fun t => QuantumZipper.TV.tvDist (μ t) (ν t)) l (𝓝 0)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist ((μ t).map (f t))
      ((ν t).map (f t))) l (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · exact Eventually.of_forall fun _ => bot_le
  · exact Eventually.of_forall fun t => QuantumZipper.TV.tvDist_map_le (hf t)

/-- Measurable images of countable phases converge to the corresponding images
    of the uniformized law under fiberwise absolute continuity. -/
theorem tendsto_tvDist_countablePhaseMap_image
    {E β τ : Type*} [MeasurableSpace E] [MeasurableSpace β] {l : Filter τ}
    (μ : Measure (CountablePhaseSpace E)) [IsFiniteMeasure μ]
    (hμ : ∀ n : ℕ,
      let ν := μ.comap (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n)
      ν ≪ (ν.map Prod.fst).prod (volume : Measure (Fin n → ℝ)))
    (a : τ → ℝ) (ha : Tendsto a l atTop)
    (θ : τ → ∀ k, E → (Fin k → ℝ)) (hθ : ∀ t k, Measurable (θ t k))
    (f : τ → CountablePhaseSpace E → β) (hf : ∀ t, Measurable (f t)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      ((μ.map (countablePhaseMap (a t) (θ t))).map (f t))
      ((countableUniformPhaseKernel ∘ₘ μ).map (f t))) l (𝓝 0) := by
  exact tendsto_tvDist_map_of_tendsto _ _ f hf
    (tendsto_tvDist_countablePhaseMap μ hμ a ha θ hθ)

end LatticeProb
