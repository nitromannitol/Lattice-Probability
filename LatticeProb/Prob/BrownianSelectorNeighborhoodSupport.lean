import LatticeProb.Prob.SelectorCommonNeighborhood
import LatticeProb.Euclidean.ParentBlockExitGeometry
import LatticeProb.Bonanno.BouRabeeGwynne.HarmonicNearClosureBrownianExit

/-! # Supported endpoints and common neighborhoods -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne

namespace LatticeProb

/-- If the second marginal is supported on the active region, the entire
common-neighborhood failure event is controlled by disagreement or separation. -/
theorem measure_not_common_selected_neighborhood_le_of_snd_ae
    {X J : Type*} [PseudoMetricSpace X] [MeasurableSpace X]
    (f : X → Option J) (C : Set X) (G : J → Set X) {r : ℝ} (hr : 0 < r)
    (hactive : ∀ y ∈ C, f y ≠ none)
    (hmargin : ∀ y j, f y = some j → ball y r ⊆ G j)
    (π : Measure (X × X)) (hC : ∀ᵐ y ∂π.snd, y ∈ C) :
    π {p | ¬ ∃ j, f p.1 = some j ∧ f p.2 = some j ∧
        p.1 ∈ G j ∧ p.2 ∈ G j} ≤
      π {p | f p.1 ≠ f p.2 ∨ r ≤ dist p.1 p.2} := by
  apply measure_mono_ae
  have hC' : ∀ᵐ p ∂π, p.2 ∈ C :=
    MeasureTheory.ae_of_ae_map measurable_snd.aemeasurable hC
  filter_upwards [hC'] with p hp hfail
  by_contra hn
  have heq : f p.1 = f p.2 := by
    by_contra hne
    exact hn (Or.inl hne)
  have hdist : dist p.1 p.2 < r := by
    by_contra hle
    exact hn (Or.inr (le_of_not_gt hle))
  exact hfail (exists_common_selected_neighborhood f C G hr hactive hmargin hp heq hdist)

namespace ParentBlock

/-- The stopped Brownian endpoint belongs almost surely to the parent block
containing its exit ball. -/
theorem stoppedBrownianLaw_endPoint_ae_mem_parentBlock
    (c : ℂ) {S r : ℝ} (hS : 0 ≤ S) (hr : r ≤ S)
    (a x : Euc 2)
    (ha : Complex.orthonormalBasisOneI.repr.symm a ∈ closedSquare c S)
    (hx : x ∈ ball a r)
    (ρ : Measure (BrownianPath 2)) (hρ : IsStandardBrownianLaw ρ) :
    ∀ᵐ y ∂((stoppedBrownianLaw (ball a r) x ρ).map CurveSpace.endPoint),
      y ∈ Complex.orthonormalBasisOneI.repr.symm ⁻¹' parentBlock c S := by
  filter_upwards [standardBrownianLaw_stopped_endPoint_ae_mem_frontier
    (by norm_num : (0 : ℕ) < 2) hρ isOpen_ball isBounded_ball hx] with y hy
  exact frontier_ball_subset_parentBlock_preimage hS hr ha hy

end ParentBlock
end LatticeProb
