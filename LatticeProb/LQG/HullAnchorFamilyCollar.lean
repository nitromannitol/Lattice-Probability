import LatticeProb.LQG.HullCollarGerm

/-! # Anchor family and collar observation germs -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF

namespace LatticeProb.LQG

/-- A family of hull anchor observations and the collar codes generate the
same germ when both have uniformly supported unit-integral anchors. -/
theorem iInf_iSup_localHullFieldSigma_eq_iInf_collarFieldCode {Ω : Type} {I : Type*}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (K : Ω → NonemptyCompacts ℂ)
    (z : ℂ) (hz : ∀ ω, z ∈ (K ω : Set ℂ))
    (α : I → TestC) (i : ℕ → I) (hα : ∀ j, ∫ x, α j x = 1)
    (hαsupp : ∀ n ω, tsupport (α (i n) : ℂ → ℝ) ⊆
      interior (dyadicHull n (K ω : Set ℂ)))
    (ψ : ℕ → TestC) (hψ : ∀ k, ∫ x, ψ k x = 1)
    (hψsupp : ∀ k ω, tsupport (ψ k : ℂ → ℝ) ⊆
      thickening (1 / ((k : ℝ) + 1)) (K ω : Set ℂ))
    {p : ℝ} (hp : 0 < p) :
    (⨅ n, ⨆ j, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (α j) hp) =
      ⨅ k, MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance := by
  rw [iInf_iSup_localHullFieldSigma_eq h (fun ω => (K ω : Set ℂ))
    (fun ω => (K ω).isCompact.isBounded) α i hα hαsupp hp]
  exact iInf_localHullFieldSigma_eq_iInf_collarFieldCode h K z hz
    (fun n => α (i n)) ψ (fun n => hα (i n)) hαsupp hψ hψsupp hp

end LatticeProb.LQG
