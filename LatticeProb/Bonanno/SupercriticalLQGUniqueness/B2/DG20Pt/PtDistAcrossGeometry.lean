/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAcrossGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PercFieldAll
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Annulus

 

set_option autoImplicit false
noncomputable section

open Set Metric TopologicalSpace

namespace SupercriticalLQGUniqueness.B2.DG20Pt

def ptAcrossU : Opens ℂ := ⟨ball 0 17, isOpen_ball⟩

theorem ptAcross_data :
    IsCompact (sphere (0 : ℂ) (1 / 4)) ∧
    IsCompact (sphere (0 : ℂ) 16) ∧
    IsConnected (sphere (0 : ℂ) (1 / 4)) ∧
    IsConnected (sphere (0 : ℂ) 16) ∧
    (sphere (0 : ℂ) (1 / 4)).Nontrivial ∧
    (sphere (0 : ℂ) 16).Nontrivial ∧
    sphere (0 : ℂ) (1 / 4) ⊆ ptAcrossU ∧
    sphere (0 : ℂ) 16 ⊆ ptAcrossU ∧
    Disjoint (sphere (0 : ℂ) (1 / 4)) (sphere (0 : ℂ) 16) ∧
    IsConnected (ptAcrossU : Set ℂ) := by
  have hnt₁ := Strong.nontrivial_sphere (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 4)
  have hnt₂ := Strong.nontrivial_sphere (0 : ℂ) (by norm_num : (0 : ℝ) < 16)
  refine ⟨isCompact_sphere _ _, isCompact_sphere _ _, ?_, ?_, hnt₁, hnt₂,
    ?_, ?_, ?_, ?_⟩
  · exact ⟨hnt₁.nonempty,
      LQGMetric.TopoCircle.isPreconnected_sphere_complex _ (by norm_num)⟩
  · exact ⟨hnt₂.nonempty,
      LQGMetric.TopoCircle.isPreconnected_sphere_complex _ (by norm_num)⟩
  · intro z hz
    change z ∈ ball (0 : ℂ) 17
    exact (mem_ball.mpr) (by rw [mem_sphere.mp hz]; norm_num)
  · intro z hz
    change z ∈ ball (0 : ℂ) 17
    exact (mem_ball.mpr) (by rw [mem_sphere.mp hz]; norm_num)
  · apply Set.disjoint_left.mpr
    intro z hz₁ hz₂
    have h₁ := mem_sphere.mp hz₁
    have h₂ := mem_sphere.mp hz₂
    linarith
  · change IsConnected (ball (0 : ℂ) 17)
    exact (convex_ball (0 : ℂ) 17).isConnected (nonempty_ball.mpr (by norm_num))

theorem ptAcross_scale_ball {r : ℝ} (hr : 0 < r) :
    (fun z : ℂ => (r : ℂ) * z) '' ptAcrossU = ball (0 : ℂ) (17 * r) := by
  have hcr : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := smul_ball hcr (0 : ℂ) 17
  change (fun z : ℂ => (r : ℂ) * z) '' ball 0 17 =
    ball ((r : ℂ) * 0) (‖(r : ℂ)‖ * 17) at h
  change (fun z : ℂ => (r : ℂ) * z) '' ball 0 17 = ball 0 (17 * r)
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, mul_zero, mul_comm 17 r] using h

theorem ptAcross_scale_sphere {r a : ℝ} (hr : 0 < r) :
    (fun z : ℂ => (r : ℂ) * z) '' sphere (0 : ℂ) a =
      sphere (0 : ℂ) (a * r) := by
  have hcr : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h := smul_sphere' hcr (0 : ℂ) a
  change (fun z : ℂ => (r : ℂ) * z) '' sphere 0 a =
    sphere ((r : ℂ) * 0) (‖(r : ℂ)‖ * a) at h
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hr, mul_zero, mul_comm a r] using h

theorem ptAcross_translate_ball (x : ℂ) (R : ℝ) :
    (fun z : ℂ => z + x) '' ball 0 R = ball x R := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_right,
      sub_zero] using hz
  · intro hw
    refine ⟨w - x, ?_, by ring⟩
    simpa only [mem_ball, dist_eq_norm, sub_zero] using hw

theorem ptAcross_translate_sphere (x : ℂ) (R : ℝ) :
    (fun z : ℂ => z + x) '' sphere 0 R = sphere x R := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa only [mem_sphere, dist_eq_norm, add_sub_cancel_right,
      sub_zero] using hz
  · intro hw
    refine ⟨w - x, ?_, by ring⟩
    simpa only [mem_sphere, dist_eq_norm, sub_zero] using hw

end SupercriticalLQGUniqueness.B2.DG20Pt
