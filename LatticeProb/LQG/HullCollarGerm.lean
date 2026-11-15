import LatticeProb.LQG.HullPhaseCollar
import LatticeProb.LQG.UniformCollarHull

/-! # Comparison of hull and collar observation germs -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- Fixed supported anchors give the same germ of local hull observations and
collar codes when the compact sets share a point. -/
theorem iInf_localHullFieldSigma_eq_iInf_collarFieldCode {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (hz : ∀ ω, z ∈ (K ω : Set ℂ))
    (a ψ : ℕ → TestC) (ha : ∀ n, ∫ x, a n x = 1)
    (hasupp : ∀ n ω, tsupport (a n : ℂ → ℝ) ⊆
      interior (dyadicHull n (K ω : Set ℂ)))
    (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hψsupp : ∀ k ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    (⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp) =
      ⨅ k, MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance := by
  apply le_antisymm
  · apply le_iInf
    intro k
    obtain ⟨f, hf⟩ := exists_dyadicHull_scales_subset_reciprocal_thickening
    exact (iInf_le (fun n => localHullFieldSigma h
      (fun ω => (K ω : Set ℂ)) n (a n) hp) (f k)).trans
      (localHullFieldSigma_le_collarFieldCode h K ψ hp k (f k) (a (f k))
        (ha (f k)) (hasupp (f k)) (fun ω => hf k (K ω : Set ℂ)))
  · apply le_iInf
    intro n
    obtain ⟨b, hb, hbsupp, hle⟩ :=
      iInf_collarFieldCode_le_localHullFieldSigma h K n z hz localDenseTest ψ hψ hψsupp hp
    exact hle.trans (localHullFieldSigma_le_of_anchor_supported h
      (fun ω => (K ω : Set ℂ)) (fun ω => (K ω).isCompact.isBounded)
      n (a n) b (ha n) hb (hasupp n) hp)

end LatticeProb.LQG
