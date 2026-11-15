import LatticeProb.LQG.CompactSelectedHullRestriction
import LatticeProb.LQG.DyadicHullAnchors

/-! # Selected collar observations with a common point -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A common point gives a deterministic normalized hull anchor and a measurable
selected collar whose gated field observations are measurable from the hull. -/
theorem exists_anchor_measurable_collar_hull_restriction {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ) (n : ℕ)
    (z : ℂ) (hz : ∀ ω, z ∈ (K ω : Set ℂ)) (φ : I → TestC)
    {p : ℝ} (hp : 0 < p) :
    ∃ ψ : TestC, (∫ x, ψ x) = 1 ∧
      (∀ ω, tsupport (ψ : ℂ → ℝ) ⊆ interior (dyadicHull n (K ω : Set ℂ))) ∧
      ∃ f : Ω → ℕ, Measurable[setSigma (fun ω => (K ω : Set ℂ))] f ∧
        (∀ ω, thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ) ⊆
          interior (dyadicHull n (K ω : Set ℂ))) ∧
        Measurable[localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n ψ hp]
          (fun (ω : Ω) =>
            ((fun i =>
              let E : Set Ω := {ω | tsupport (φ i : ℂ → ℝ) ⊆
                thickening (1 / ((f ω : ℝ) + 1)) (K ω : Set ℂ)}
              (E.indicator (fun _ => (1 : ℝ)) ω,
                E.indicator (fun ω => h ω (φ i) - (∫ x, φ i x) * h ω ψ) ω)),
             toIcoMod hp 0 (h ω ψ))) := by
  obtain ⟨ψ, hψ⟩ := exists_dyadicHull_anchors z
  have hsupport : ∀ ω, tsupport (ψ n : ℂ → ℝ) ⊆
      interior (dyadicHull n (K ω : Set ℂ)) := fun ω => (hψ n).2 _ (hz ω)
  refine ⟨ψ n, (hψ n).1, hsupport, ?_⟩
  exact exists_measurable_collar_hull_restriction h K n φ (ψ n) (hψ n).1 hsupport hp

end LatticeProb.LQG
