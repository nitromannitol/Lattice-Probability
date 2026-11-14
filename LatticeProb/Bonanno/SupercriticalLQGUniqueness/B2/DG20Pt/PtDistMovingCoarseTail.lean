/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingCoarseTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistMovingPathCost

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP LQGMetric.DG

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_moving_fixed_scale_upper_tail_small
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (ξ : Ioi (0 : ℝ))
    (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (z w : ℂ) (hz : z ∈ U) (hw : w ∈ U)
    (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧
      ∀ r : ℝ, 1 ≤ r → r ≤ 2 →
        P {ω | ¬ lfppDOn (ξ : ℝ)
          (fun y => phiMN W P 0 n y ω)
          ((fun x : ℂ => (r : ℂ) * x) '' U)
          ((r : ℂ) * z) ((r : ℂ) * w) ≤
            ENNReal.ofReal (M * lambdaN ξ W P n)} ≤
          ENNReal.ofReal ε := by
  obtain ⟨q, hq⟩ := t15_exists_isDGPath hU hUc hz hw
  let K : Set ℂ := q '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hq.continuousOn
  let Mset : Set ℂ :=
    (fun p : ℝ × ℂ => (p.1 : ℂ) * p.2) '' (Icc (1 : ℝ) 2 ×ˢ K)
  have hMset : IsCompact Mset := (isCompact_Icc.prod hK).image (by fun_prop)
  obtain ⟨L, hL, htail⟩ :=
    pt_dist_compact_phiMN_sup_tail_small P W hW n Mset hMset ε hε
  have hqpath : IsPiecewiseC1Path q z w :=
    ⟨hq.source, hq.target, hq.continuousOn, hq.piecewise_contDiff⟩
  have hAdm : LQGMetric.DDDF.AdmPath K {z} {w} q := by
    refine ⟨z, by simp, w, by simp, hqpath, ?_⟩
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hfin : lfppLen (ξ : ℝ) (fun _ : ℂ => 0) q ≠ ∞ :=
    LQGMetric.DDDF.lfppLen_ne_top_of_adm continuous_const hK hAdm
  let b : ℝ := (lfppLen (ξ : ℝ) (fun _ : ℂ => 0) q).toReal
  have hb : 0 ≤ b := ENNReal.toReal_nonneg
  have hbEq : ENNReal.ofReal b =
      lfppLen (ξ : ℝ) (fun _ : ℂ => 0) q :=
    ENNReal.ofReal_toReal hfin
  let lam : ℝ := lambdaN ξ W P n
  have hlam : 0 < lam := lambdaN_pos hW n
  let M : ℝ := 2 * Real.exp (|(ξ : ℝ)| * L) * b / lam + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hbudget : 2 * Real.exp (|(ξ : ℝ)| * L) * b ≤ M * lam := by
    dsimp [M]
    field_simp
    nlinarith
  refine ⟨M, hM, ?_⟩
  intro r hr1 hr2
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr1
  have hsub :
      {ω | ¬ lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω)
        ((fun x : ℂ => (r : ℂ) * x) '' U)
        ((r : ℂ) * z) ((r : ℂ) * w) ≤
          ENNReal.ofReal (M * lam)} ⊆
      {ω | ∃ x ∈ Mset, L < |phiMN W P 0 n x ω|} := by
    intro ω hbad
    by_contra hgood
    have hfield (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
        |phiMN W P 0 n ((r : ℂ) * q t) ω| ≤ L := by
      have hmem : (r : ℂ) * q t ∈ Mset :=
        ⟨(r, q t), ⟨⟨hr1, hr2⟩, ⟨t, ht, rfl⟩⟩, rfl⟩
      exact le_of_not_gt (fun hgt => hgood ⟨_, hmem, hgt⟩)
    have hpath := pt_dist_scaled_path_upper_of_sup (ξ : ℝ)
      (fun y => phiMN W P 0 n y ω) U z w q hq r hr0 L hfield
    have hnorm :
        ENNReal.ofReal (Real.exp (|(ξ : ℝ)| * L)) *
            (ENNReal.ofReal r * lfppLen (ξ : ℝ) (fun _ : ℂ => 0) q) ≤
          ENNReal.ofReal (M * lam) := by
      rw [← hbEq]
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ r),
        ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      apply ENNReal.ofReal_le_ofReal
      have hmult : r * b ≤ 2 * b := mul_le_mul_of_nonneg_right hr2 hb
      nlinarith [mul_nonneg (Real.exp_pos (|(ξ : ℝ)| * L)).le
        (sub_nonneg.mpr hmult)]
    exact hbad (hpath.trans hnorm)
  exact (measure_mono hsub).trans htail

end SupercriticalLQGUniqueness.B2.DG20Pt
