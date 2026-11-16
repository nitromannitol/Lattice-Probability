import LatticeProb.LQG.HullCollarGerm
import LatticeProb.LQG.DiscretePhaseRealHull

/-! # Collar germs and local field histories -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- The mean-zero local field history is contained in the discrete-phase collar germ. -/
theorem localSigma0_le_iInf_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (hz : ∀ ω, z ∈ (K ω : Set ℂ))
    (ψ : ℕ → TestC) (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hψsupp : ∀ k ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    localSigma0 h (fun ω => (K ω : Set ℂ)) ≤
      ⨅ k, MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance := by
  obtain ⟨a, ha⟩ := exists_dyadicHull_anchors z
  have hasupp : ∀ n ω, tsupport (a n : ℂ → ℝ) ⊆
      interior (dyadicHull n (K ω : Set ℂ)) := fun n ω => (ha n).2 _ (hz ω)
  rw [← iInf_localHullFieldSigma_eq_iInf_collarFieldCode h K z hz a ψ
    (fun n => (ha n).1) hasupp hψ hψsupp hp]
  unfold localSigma0
  exact iInf_mono fun n => le_sup_left

/-- The discrete-phase collar germ is contained in the real local field history. -/
theorem iInf_collarFieldCode_le_localSigma {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (hz : ∀ ω, z ∈ (K ω : Set ℂ))
    (ψ : ℕ → TestC) (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hψsupp : ∀ k ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    (⨅ k, MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance) ≤
      localSigma h (fun ω => (K ω : Set ℂ)) := by
  obtain ⟨a, ha⟩ := exists_dyadicHull_anchors z
  have hasupp : ∀ n ω, tsupport (a n : ℂ → ℝ) ⊆
      interior (dyadicHull n (K ω : Set ℂ)) := fun n ω => (ha n).2 _ (hz ω)
  rw [← iInf_localHullFieldSigma_eq_iInf_collarFieldCode h K z hz a ψ
    (fun n => (ha n).1) hasupp hψ hψsupp hp]
  unfold localSigma
  exact iInf_mono fun n => localHullFieldSigma_le_hullSigma h
    (fun ω => (K ω : Set ℂ)) (fun ω => (K ω).isCompact.isBounded) n (a n) hp

end LatticeProb.LQG
