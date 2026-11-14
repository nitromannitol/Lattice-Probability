/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRefYGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCDisconnectsTransport

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric Complex
open scoped ComplexConjugate
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric LQGMetric.DDDF

def laneCRefY (z : ℂ) : ℂ := conj z + Complex.I

theorem laneC_refY_re (z : ℂ) : (laneCRefY z).re = z.re := by
  simp [laneCRefY]

theorem laneC_refY_im (z : ℂ) : (laneCRefY z).im = 1 - z.im := by
  simp [laneCRefY]
  ring

theorem laneC_refY_involutive (z : ℂ) : laneCRefY (laneCRefY z) = z := by
  simp [laneCRefY, map_add]

theorem laneC_refY_continuous : Continuous laneCRefY :=
  continuous_conj.add continuous_const

theorem laneC_refY_dist (z w : ℂ) :
    dist (laneCRefY z) (laneCRefY w) = dist z w := by
  simp [laneCRefY, dist_eq_norm, ← map_sub]

theorem laneC_refY_sphere (c : ℂ) (r : ℝ) :
    laneCRefY '' sphere c r = sphere (laneCRefY c) r := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa only [mem_sphere, laneC_refY_dist] using hw
  · intro hz
    refine ⟨laneCRefY z, ?_, laneC_refY_involutive z⟩
    rw [mem_sphere] at hz ⊢
    have heq := laneC_refY_dist (laneCRefY z) c
    rw [laneC_refY_involutive] at heq
    rw [← heq]
    exact hz

theorem laneC_refY_square {z : ℂ}
    (hz : z ∈ (rectAB 1 1).toSet) :
    laneCRefY z ∈ (rectAB 1 1).toSet := by
  rw [mem_rectAB_toSet] at hz ⊢
  rw [laneC_refY_re, laneC_refY_im]
  rcases hz with ⟨⟨hx0, hx1⟩, ⟨hy0, hy1⟩⟩
  exact ⟨⟨hx0, hx1⟩, ⟨by linarith, by linarith⟩⟩

theorem laneC_refY_left {z : ℂ}
    (hz : z ∈ (rectAB 1 1).side₁) :
    laneCRefY z ∈ (rectAB 1 1).side₁ := by
  rw [mem_rectAB_side₁] at hz ⊢
  rw [laneC_refY_re, laneC_refY_im]
  rcases hz with ⟨hx, hy⟩
  rw [mem_Icc] at hy ⊢
  exact ⟨hx, by linarith [hy.2], by linarith [hy.1]⟩

theorem laneC_refY_right {z : ℂ}
    (hz : z ∈ (rectAB 1 1).side₂) :
    laneCRefY z ∈ (rectAB 1 1).side₂ := by
  rw [mem_rectAB_side₂] at hz ⊢
  rw [laneC_refY_re, laneC_refY_im]
  rcases hz with ⟨hx, hy⟩
  rw [mem_Icc] at hy ⊢
  exact ⟨hx, by linarith [hy.2], by linarith [hy.1]⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
