import LatticeProb.Prob.AEPrefixStoppedHistory

/-! # Completed filtrations and stopped histories -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace LatticeProb

/-- Complete each time of a filtration using the null sets of the ambient measure. -/
def completedFiltration {Ω ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
    (F : Filtration ι m) (μ : Measure Ω) :
    Filtration ι (eventuallyMeasurableSpace m (ae μ)) where
  seq t := eventuallyMeasurableSpace (F t) (ae μ)
  mono' := by
    intro s t hst A hA
    obtain ⟨B, hB, hAB⟩ := hA
    exact ⟨B, F.mono hst B hB, hAB⟩
  le' := by
    intro t A hA
    obtain ⟨B, hB, hAB⟩ := hA
    exact ⟨B, F.le t B hB, hAB⟩

/-- An event in a completed natural stopping history has an almost surely equal
representative observable from a strictly later clock and stopped path. -/
theorem completed_stopped_history_representative_of_lt
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (S T : Ω → ℝ≥0∞) (μ : Measure Ω)
    (hS : IsStoppingTime (completedFiltration (natFiltration X hm) μ) S)
    (hST : ∀ᵐ ω ∂μ, S ω < T ω)
    {A : Set Ω} (hA : MeasurableSet[hS.measurableSpace] A) :
    ∃ B : Set Ω, MeasurableSet[MeasurableSpace.comap
      (fun ω => (T ω, stoppedPath (T ω) (pathMap X hc ω))) inferInstance] B ∧
      ∀ᵐ ω ∂μ, ω ∈ A ↔ ω ∈ B := by
  apply ae_prefix_history_representative_of_lt hm hc S T μ hST
  intro t
  have hprefix := ((hS.measurableSet A).1 hA).2 t
  exact hprefix

end LatticeProb
