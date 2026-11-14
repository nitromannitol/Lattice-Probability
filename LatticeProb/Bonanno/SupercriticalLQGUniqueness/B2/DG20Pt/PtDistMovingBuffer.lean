/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingBuffer at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingCollar
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistBufferedRegion

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_moving_buffer {K : Set ℂ} (hK : IsCompact K) :
    ∃ V : Set ℂ, Bornology.IsBounded V ∧ Convex ℝ V ∧
      ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
        ∀ v ∈ K, ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
          closedBall ((r : ℂ) * v) ρ ⊆ V := by
  let M : Set ℂ := (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) ''
    (Icc (1 : ℝ) 2 ×ˢ K)
  have hM : IsCompact M := by
    exact (isCompact_Icc.prod hK).image (by fun_prop)
  obtain ⟨V, hV, hconv, hbuffer⟩ :=
    pt_dist_compact_buffered_region hM
  refine ⟨V, hV, hconv, ?_⟩
  intro r hr1 hr2 v hv ρ hρ0 hρ1
  have hrv : (r : ℂ) * v ∈ M :=
    ⟨(r, v), ⟨⟨hr1, hr2⟩, hv⟩, rfl⟩
  exact hbuffer _ hrv ρ hρ0 hρ1

end SupercriticalLQGUniqueness.B2.DG20Pt
