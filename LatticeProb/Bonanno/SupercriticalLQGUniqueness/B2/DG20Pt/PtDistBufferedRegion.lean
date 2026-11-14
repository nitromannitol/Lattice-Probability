/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistBufferedRegion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainTriangle

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_compact_buffered_region
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ V : Set ℂ, Bornology.IsBounded V ∧ Convex ℝ V ∧
      ∀ v ∈ K, ∀ r : ℝ, 0 ≤ r → r ≤ 1 → closedBall v r ⊆ V := by
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let V : Set ℂ := closedBall 0 (max R₀ 0 + 2)
  refine ⟨V, isBounded_closedBall, convex_closedBall 0 _, ?_⟩
  intro v hv r hr hr1 x hx
  have hvR : dist (0 : ℂ) v ≤ R₀ := by simpa only [dist_comm] using (mem_closedBall.mp (hR₀ hv))
  have hxr : dist v x ≤ r := by simpa only [dist_comm] using (mem_closedBall.mp hx)
  have htri := dist_triangle (0 : ℂ) v x
  change x ∈ closedBall 0 (max R₀ 0 + 2)
  rw [mem_closedBall, dist_comm]
  have hRmax : R₀ ≤ max R₀ 0 := le_max_left _ _
  linarith

end SupercriticalLQGUniqueness.B2.DG20Pt
