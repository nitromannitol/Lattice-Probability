import LatticeProb.LQG.DyadicHullAnchors
import LatticeProb.Topology.CompactPrefixInterval

/-! # Anchors for stopped path prefixes -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.LocalEvent
open scoped ENNReal NNReal

namespace LatticeProb.LQG

/-- A fixed starting point admits normalized anchors supported in every dyadic
hull of every finite stopped prefix beginning there. The same anchors apply to
the observed stopped path and to the original path on the stopping interval. -/
theorem exists_dyadicHull_stoppedPrefix_anchors (z : ℂ) :
    ∃ ψ : ℕ → TestC, (∀ n, ∫ x, ψ n x = 1) ∧
      ∀ (w : C(ℝ≥0, ℂ)) (T : ℝ≥0∞), T ≠ ∞ → w 0 = z → ∀ n,
        tsupport (ψ n : ℂ → ℝ) ⊆
          interior (dyadicHull n (w '' Icc 0 T.toNNReal)) ∧
        tsupport (ψ n : ℂ → ℝ) ⊆
          interior (dyadicHull n
            (compactPathPrefix (stoppedPath T w) T.toNNReal : Set ℂ)) := by
  obtain ⟨ψ, hψ⟩ := exists_dyadicHull_anchors z
  refine ⟨ψ, (fun n => (hψ n).1), ?_⟩
  intro w T hT hw n
  have hz : z ∈ w '' Icc 0 T.toNNReal := by
    rw [← hw]
    exact Set.mem_image_of_mem w ⟨le_rfl, zero_le⟩
  have hs := (hψ n).2 (w '' Icc 0 T.toNNReal) hz
  exact ⟨hs, by rw [coe_compactPathPrefix_stoppedPath w T hT]; exact hs⟩

end LatticeProb.LQG
