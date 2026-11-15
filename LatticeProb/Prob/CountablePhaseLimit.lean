import LatticeProb.Prob.CountablePhaseTransport

/-! Phase convergence on a fixed fiber of a countable disjoint union. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LatticeProb

/-- An embedded finite fixed-count measure with an absolutely continuous
coordinate law has asymptotically uniform phases in total variation. -/
theorem tendsto_tvDist_countablePhaseMap_fixedCount
    {E τ : Type*} [MeasurableSpace E] {l : Filter τ}
    (n : ℕ) (μ : Measure (E × (Fin n → ℝ))) [IsFiniteMeasure μ]
    (hμ : μ ≪ (μ.map Prod.fst).prod (volume : Measure (Fin n → ℝ)))
    (a : τ → ℝ) (ha : Tendsto a l atTop)
    (θ : τ → ∀ k, E → (Fin k → ℝ)) (hθ : ∀ t k, Measurable (θ t k)) :
    Tendsto (fun t => QuantumZipper.TV.tvDist
      ((μ.map (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n)).map
        (countablePhaseMap (a t) (θ t)))
      (countableUniformPhaseKernel ∘ₘ
        (μ.map (@Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n)))) l (𝓝 0) := by
  let j := @Sigma.mk ℕ (fun k => E × (Fin k → ℝ)) n
  have hj : Measurable j := by
    intro s hs
    change MeasurableSet[⨅ i : ℕ, (inferInstance : MeasurableSpace (E × (Fin i → ℝ))).map
      (Sigma.mk i)] s at hs
    exact (MeasurableSpace.measurableSet_iInf.mp hs) n
  have h := tendsto_tvDist_phase_of_absolutelyContinuous n μ hμ a ha
    (fun t => θ t n) (fun t => hθ t n)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
  · exact Eventually.of_forall fun _ => bot_le
  · apply Eventually.of_forall
    intro t
    rw [countablePhaseMap_map n μ (a t) (θ t) (hθ t),
      countableUniformPhaseKernel_comp_map n μ]
    exact QuantumZipper.TV.tvDist_map_le hj

end LatticeProb
