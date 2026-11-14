/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBPerimeterSeparator at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteExitMeet
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.LFPP LQGMetric.DDDF

 



theorem laneB_perimeter_separating_walk {ξ : ℝ} {f : ℂ → ℝ}
    (hf : Continuous f) {R bnd : ℝ} (hR : 24 ≤ R)
    (hfamily : ∀ j ∈ laneBLongRects R,
      T20B.mrectLen ξ f 0 j.1 j.2 3 1 ≤ bnd)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ (V : ℝ → ℂ) (a d : ℂ),
      IsPiecewiseC1Path V a d ∧
      MapsTo V (Icc (0 : ℝ) 1)
        {z : ℂ | R < dist z 0 ∧ dist z 0 < 2 * R} ∧
      LQGMetric.Disconnects (V '' Icc (0 : ℝ) 1)
        (sphere 0 R) (sphere 0 (2 * R)) ∧
      lfppLen ξ f V ≤
        (((4 * (2 * laneBGridRadius R + 1)).toNat + 1 : ℕ) : ℝ≥0∞) *
          (3 * (3 * (4 * (ENNReal.ofReal bnd + δ)))) := by
  obtain ⟨V, a, d, hp, hmap, hcircs, hlen⟩ :=
    laneB_perimeter_walk hf hR hfamily hδ
  refine ⟨V, a, d, hp, hmap, ?_, hlen⟩
  intro x y γ hx hy
  have hstart : ‖γ.extend 0‖ = R := by
    simpa [Path.extend_zero, Metric.mem_sphere, dist_eq_norm] using hx
  have hend : ‖γ.extend 1‖ = 2 * R := by
    simpa [Path.extend_one, Metric.mem_sphere, dist_eq_norm] using hy
  obtain ⟨t, ht, b, hb, hvisit⟩ :=
    laneB_annulus_crossing_visits_boundaryFamily hR
      γ.continuous_extend.continuousOn hstart hend
  obtain ⟨C, hC⟩ := hcircs b hb
  let Q := Strong.seg γ.extend t 0
  have hzero : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have hQc : ContinuousOn Q (Icc (0 : ℝ) 1) :=
    Strong.continuousOn_seg γ.continuous_extend.continuousOn ht hzero
  have hQstart : Q 0 ∈ T20.dyBlock 0 b := by simpa [Q] using hvisit
  have hQend : Q 1 ∉
      Ioo ((b.1 : ℝ) - 1) ((b.1 : ℝ) + 2) ×ℂ
        Ioo ((b.2 : ℝ) - 1) ((b.2 : ℝ) + 2) := by
    intro hmem
    have hbox : Q 1 ∈ T20D.hatBox 0 b := by
      simp only [T20D.hatBox, pow_zero, mul_one, Complex.mem_reProdIm,
        mem_Ioo, mem_Icc] at hmem ⊢
      exact ⟨⟨hmem.1.1.le, hmem.1.2.le⟩,
        hmem.2.1.le, hmem.2.2.le⟩
    have hnot := laneB_inner_sphere_outside_boundary_hatBox hR hb hstart
    apply hnot
    simpa only [Q, Strong.seg_one, Path.extend_zero] using hbox
  obtain ⟨r, hr, hmeet⟩ :=
    laneB_siteCirc_meets_exit C zero_le_one hQc hQstart hQend
  have hr' : t + r * (0 - t) ∈ Icc (0 : ℝ) 1 :=
    Strong.seg_param_mem ht hzero hr
  have hpoint : γ.extend (t + r * (0 - t)) ∈ V '' Icc (0 : ℝ) 1 := by
    apply hC
    simpa only [Q, Strong.seg] using hmeet
  refine ⟨γ.extend (t + r * (0 - t)), ?_, hpoint⟩
  exact ⟨⟨t + r * (0 - t), hr'⟩, (γ.extend_apply hr').symm⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
