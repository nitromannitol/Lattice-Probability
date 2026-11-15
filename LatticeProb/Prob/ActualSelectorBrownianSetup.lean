import LatticeProb.Bonanno.BouRabeeGwynne.TheoremACouplingSetup
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianCoupling

/-! # Brownian estimates for walk-selected excursions -/

set_option autoImplicit false

open MeasureTheory Set Metric BouRabeeGwynne
open scoped unitInterval ENNReal

namespace LatticeProb

local instance {X : Type*} : MeasurableSpace (Option X) := ⊤

/-- The fixed Brownian setup also controls the shifted selectors used by the
walk coupling, with the oscillation bound expressed on Brownian paths. -/
theorem exists_actual_selector_brownian_setup {d : ℕ} (hd : 1 ≤ d)
    {U D : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : HasLipschitzBoundary U) (hUD : HasAmbientCollar U D)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {η : ℝ} (hη : 0 < η) :
    ∃ (δ r : ℝ) (W Q : Set (Euc d)) (centers : Finset (Euc d)) (K : ℕ),
      0 < δ ∧ 0 < r ∧ r ≤ δ / 100 ∧ r ≤ η / 100 ∧
      IsOpen W ∧ Bornology.IsBounded W ∧ U ⊆ W ∧ HasAmbientCollar W D ∧
      IsCompact Q ∧ cthickening δ U ⊆ Q ∧
      (∀ c ∈ centers, c ∈ cthickening δ U) ∧
      (∀ z ∈ cthickening δ U, ∃ c ∈ centers, z ∈ ball c (r / 4)) ∧
      (∀ c ∈ centers, closedBall c r ⊆ W) ∧
      (∀ c ∈ centers, closure (ball c r) ⊆ Q) ∧
      ∀ z ∈ U, ∀ j₀ : ↥centers,
      ∀ (select : ℕ → Euc d → Option ↥centers) (_hs : ∀ k, Measurable (select k)),
      (∀ k x j, select k x = some j → ball x (r / 2) ⊆ ball (j : Euc d) r) →
      (∀ k x, x ∈ cthickening δ U → select k x ≠ none) →
      ∀ P : TimePartition K,
        μ {ω | (brownianSkeletonExcursion (fun c : ↥centers => ball (c : Euc d) r)
          z j₀ (brownianSelectorForWalk select) K ω).1 = false} ≤ ENNReal.ofReal (η / 100) ∧
        μ {ω | pastedBrownianCurve P (fun k => brownianSkeletonExcursion
          (fun c : ↥centers => ball (c : Euc d) r) z j₀ (brownianSelectorForWalk select) k ω) ∈
            unitCurveExitOscillationBad (innerDomain U (6 * r)) (thickening δ U) (η / 10)} ≤
          2 * ENNReal.ofReal (η / 100) := by
  obtain ⟨δ, r, W, Q, centers, K, hδ, hr, hrδ, hrη, hW, hWb, hUW, hWD,
    hQ, hCQ, hcenters, hcover, hballs, hballsQ, hprob⟩ :=
    exists_theoremA_coupling_setup hd hU hUb hL hUD hμ hη
  refine ⟨δ, r, W, Q, centers, K, hδ, hr, hrδ, hrη, hW, hWb, hUW, hWD,
    hQ, hCQ, hcenters, hcover, hballs, hballsQ, ?_⟩
  intro z hz initial select hs hmargin hactive P
  have hnone : ∀ i x, brownianSelectorForWalk select i x = none → x ∉ thickening δ U := by
    intro i x hi hx
    exact hactive (i - 1) x (thickening_subset_cthickening δ U hx) hi
  have hprobz := hprob z hz initial (brownianSelectorForWalk select)
    (fun i => hs (i - 1)) (fun i x j hj => hmargin (i - 1) x j hj) hnone P
  have hΓ : Measurable (fun ω k => brownianSkeletonExcursion
      (fun c : centers => ball c.val r) z initial (brownianSelectorForWalk select) k ω) :=
    Measurable.of_eval fun k => measurable_brownianSkeletonExcursion
      (fun c : centers => ball c.val r) (fun _ => isOpen_ball) z initial
      (fun i => hs (i - 1)) k
  have hset : MeasurableSet {γ : ℕ → Bool × C(unitInterval, Euc d) |
      pastedBrownianCurve P γ ∈
        unitCurveExitOscillationBad (innerDomain U (6 * r)) (thickening δ U) (η / 10)} :=
    (measurableSet_unitCurveExitOscillationBad (isOpen_innerDomain U (6 * r))
      isOpen_thickening (η / 10)).preimage (measurable_pastedBrownianCurve P)
  refine ⟨?_, ?_⟩
  · simpa only [brownianSkeletonExcursion_flag] using hprobz.1
  · rw [Measure.map_apply hΓ hset] at hprobz
    exact hprobz.2

end LatticeProb
