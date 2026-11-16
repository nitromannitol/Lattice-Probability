import LatticeProb.LQG.StoppedPrefixFieldGerm

/-! # Ambient field observations on stopped prefixes -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint
open scoped ENNReal NNReal

namespace LatticeProb.LQG

/-- For paths rooted at a common point, hull and collar field observations
give the same ambient germ after adjoining the stopped path and its clock.
At an infinite clock, the compact prefix is totalized to the initial point. -/
theorem exists_ambient_stoppedPrefix_field_germ_eq {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (w : Ω → C(ℝ≥0, ℂ)) (T : Ω → ℝ≥0∞)
    (z : ℂ) (hw : ∀ ω, w ω 0 = z) {p : ℝ} (hp : 0 < p) :
    ∃ a ψ : ℕ → TestC,
      (∀ n, ∫ x, a n x = 1) ∧ (∀ k, ∫ x, ψ k x = 1) ∧
      let K := fun ω => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
      (MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance ⊔
        (⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp)) =
      (MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance ⊔
        (⨅ k, MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance)) := by
  obtain ⟨a, ha⟩ := exists_dyadicHull_anchors z
  obtain ⟨ψ, hψ⟩ := exists_reciprocal_collar_anchors z
  let K := fun ω => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
  have hz : ∀ ω, z ∈ (K ω : Set ℂ) := by
    intro ω
    rw [coe_compactPathPrefix_eq_image_Icc, ← hw ω]
    exact ⟨0, ⟨le_rfl, zero_le⟩, by simp⟩
  refine ⟨a, ψ, (fun n => (ha n).1), (fun k => (hψ k).1), ?_⟩
  change (MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance ⊔
      (⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp)) =
    (MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance ⊔
      (⨅ k, MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance))
  rw [iInf_localHullFieldSigma_eq_iInf_collarFieldCode h K z hz a ψ
    (fun n => (ha n).1) (fun n ω => (ha n).2 _ (hz ω))
    (fun k => (hψ k).1) (fun k ω => (hψ k).2 _ (hz ω)) hp]

end LatticeProb.LQG
