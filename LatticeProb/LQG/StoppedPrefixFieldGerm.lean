import LatticeProb.LQG.HullCollarGerm
import LatticeProb.LQG.ReciprocalCollarAnchors
import LatticeProb.LQG.StoppedPrefixAnchors

/-! # Discrete field observations on stopped path prefixes -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric TopologicalSpace LQGMetric LQGMetric.Blueprint LQGMetric.CONF
open scoped ENNReal NNReal

namespace LatticeProb.LQG

/-- For finite stopped paths with a common starting point, the hull and collar
field germs give the same history after adjoining the stopped path and clock. -/
theorem exists_stoppedPrefix_field_germ_eq {Ω : Type}
    [MeasurableSpace (NonemptyCompacts ℂ)] [BorelSpace (NonemptyCompacts ℂ)]
    (h : Ω → DistC) (w : Ω → C(ℝ≥0, ℂ)) (T : Ω → ℝ≥0∞)
    (z : ℂ) (hw : ∀ ω, w ω 0 = z) (hT : ∀ ω, T ω ≠ ∞)
    {p : ℝ} (hp : 0 < p) :
    ∃ a ψ : ℕ → TestC,
      (∀ n, ∫ x, a n x = 1) ∧ (∀ k, ∫ x, ψ k x = 1) ∧
      let K := fun ω => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
      (∀ ω, (K ω : Set ℂ) = w ω '' Icc 0 (T ω).toNNReal) ∧
      (MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance ⊔
        (⨅ n, localHullFieldSigma h (fun ω => (K ω : Set ℂ)) n (a n) hp)) =
      (MeasurableSpace.comap (fun ω => (stoppedPath (T ω) (w ω), T ω)) inferInstance ⊔
        (⨅ k, MeasurableSpace.comap (collarFieldCode h K localDenseTest ψ hp k) inferInstance)) := by
  obtain ⟨a, ha, hasupp⟩ := exists_dyadicHull_stoppedPrefix_anchors z
  obtain ⟨ψ, hψ⟩ := exists_reciprocal_collar_anchors z
  let K := fun ω => compactPathPrefix (stoppedPath (T ω) (w ω)) (T ω).toNNReal
  have hK : ∀ ω, (K ω : Set ℂ) = w ω '' Icc 0 (T ω).toNNReal :=
    fun ω => coe_compactPathPrefix_stoppedPath (w ω) (T ω) (hT ω)
  have hz : ∀ ω, z ∈ (K ω : Set ℂ) := by
    intro ω
    rw [hK ω, ← hw ω]
    exact Set.mem_image_of_mem (w ω) ⟨le_rfl, zero_le⟩
  refine ⟨a, ψ, ha, (fun k => (hψ k).1), hK, ?_⟩
  rw [iInf_localHullFieldSigma_eq_iInf_collarFieldCode h K z hz a ψ ha
    (fun n ω => (hasupp (w ω) (T ω) (hT ω) (hw ω) n).2)
    (fun k => (hψ k).1) (fun k ω => (hψ k).2 _ (hz ω)) hp]

end LatticeProb.LQG
