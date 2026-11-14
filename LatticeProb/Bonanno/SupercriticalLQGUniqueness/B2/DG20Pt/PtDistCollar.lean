/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCollar at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistNet

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem pt_dist_eventual_crossing_ball_subset
    {V U : Set ℂ} (hV : Bornology.IsBounded V) (hU : IsOpen U)
    (hVU : closure V ⊆ U) :
    ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∀ z ∈ V, ∀ x : ℂ,
      dist z x < ((2 : ℝ)⁻¹) ^ k / 4 →
      ball x (17 * ((2 : ℝ)⁻¹) ^ k) ⊆ U := by
  obtain ⟨δ, hδ, hthick⟩ :=
    hV.isCompact_closure.exists_thickening_subset_open hU hVU
  obtain ⟨k₀, hk₀⟩ :=
    exists_pow_lt_of_lt_one (show 0 < δ / 18 by positivity)
      (show ((2 : ℝ)⁻¹) < 1 by norm_num)
  refine ⟨k₀, fun k hkk z hz x hnear y hy => ?_⟩
  have hrle : ((2 : ℝ)⁻¹) ^ k ≤ ((2 : ℝ)⁻¹) ^ k₀ :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hkk
  have hrδ : ((2 : ℝ)⁻¹) ^ k < δ / 18 := hrle.trans_lt hk₀
  have hyx : dist y x < 17 * ((2 : ℝ)⁻¹) ^ k := by
    simpa only [mem_ball] using hy
  have hyz : dist y z < δ := by
    have htri := dist_triangle y x z
    rw [dist_comm x z] at htri
    linarith
  exact hthick (mem_thickening_iff.mpr ⟨z, subset_closure hz, hyz⟩)

end SupercriticalLQGUniqueness.B2.DG20Pt
