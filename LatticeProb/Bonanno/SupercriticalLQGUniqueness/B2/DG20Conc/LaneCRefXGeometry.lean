/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRefXGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRefYGeometry

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric Complex
open scoped ComplexConjugate
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

def laneCRefX (z : ℂ) : ℂ := 1 - conj z

theorem laneC_refX_re (z : ℂ) : (laneCRefX z).re = 1 - z.re := by
  simp [laneCRefX]

theorem laneC_refX_im (z : ℂ) : (laneCRefX z).im = z.im := by
  simp [laneCRefX]

theorem laneC_refX_involutive (z : ℂ) : laneCRefX (laneCRefX z) = z := by
  simp [laneCRefX, map_sub]

theorem laneC_refX_continuous : Continuous laneCRefX :=
  continuous_const.sub continuous_conj

theorem laneC_refX_dist (z w : ℂ) :
    dist (laneCRefX z) (laneCRefX w) = dist z w := by
  simp [laneCRefX, dist_eq_norm, ← map_sub, sub_sub_sub_cancel_left]
  rw [norm_sub_rev]

theorem laneC_refX_sphere (c : ℂ) (r : ℝ) :
    laneCRefX '' sphere c r = sphere (laneCRefX c) r := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [mem_sphere, laneC_refX_dist] using hw
  · intro hz
    refine ⟨laneCRefX z, ?_, laneC_refX_involutive z⟩
    rw [mem_sphere] at hz ⊢
    have heq := laneC_refX_dist (laneCRefX z) c
    rw [laneC_refX_involutive] at heq
    rw [← heq]
    exact hz

theorem laneC_refX_square {z : ℂ}
    (hz : z ∈ (rectAB 1 1).toSet) :
    laneCRefX z ∈ (rectAB 1 1).toSet := by
  rw [mem_rectAB_toSet] at hz ⊢
  rw [laneC_refX_re, laneC_refX_im]
  rcases hz with ⟨⟨hx0, hx1⟩, hy⟩
  exact ⟨⟨by linarith, by linarith⟩, hy⟩

theorem laneC_refX_left_to_right {z : ℂ}
    (hz : z ∈ (rectAB 1 1).side₁) :
    laneCRefX z ∈ (rectAB 1 1).side₂ := by
  rw [mem_rectAB_side₁] at hz
  rw [mem_rectAB_side₂, laneC_refX_re, laneC_refX_im]
  exact ⟨by linarith [hz.1], hz.2⟩

theorem laneC_refX_right_to_left {z : ℂ}
    (hz : z ∈ (rectAB 1 1).side₂) :
    laneCRefX z ∈ (rectAB 1 1).side₁ := by
  rw [mem_rectAB_side₂] at hz
  rw [mem_rectAB_side₁, laneC_refX_re, laneC_refX_im]
  exact ⟨by linarith [hz.1], hz.2⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
