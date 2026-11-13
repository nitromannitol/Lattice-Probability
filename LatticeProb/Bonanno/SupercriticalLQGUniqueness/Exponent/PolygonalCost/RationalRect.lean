/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.Exponent.PolygonalCost.RationalRect at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.ChainInf
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18S1Geom




 



set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set

namespace SupercriticalLQGUniqueness.Exponent.PolygonalCost

open LQGMetric LQGMetric.LFPP

private theorem exists_rat_near_interval {l u x ρ : ℝ}
    (hlu : l < u) (hx : x ∈ Icc l u) (hρ : 0 < ρ) :
    ∃ q : ℚ, (q : ℝ) ∈ Icc l u ∧ |(q : ℝ) - x| < ρ := by
  have h : max l (x - ρ) < min u (x + ρ) := by
    simp only [max_lt_iff, lt_min_iff]
    exact ⟨⟨hlu, by linarith [hx.2]⟩, ⟨by linarith [hx.1], by linarith⟩⟩
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn h
  simp only [max_lt_iff] at hqlo
  simp only [lt_min_iff] at hqhi
  refine ⟨q, ⟨hqlo.1.le, hqhi.1.le⟩, ?_⟩
  exact abs_lt.mpr ⟨by linarith [hqlo.2], by linarith [hqhi.2]⟩

 
theorem gaussRat_markedRect_dense (R : DDDF.MarkedRect)
    (hw : 0 < R.w) (hh : 0 < R.h) (x : ℂ) (hx : x ∈ R.toSet)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ q ∈ gaussRat ∩ R.toSet, ‖q - x‖ < ρ := by
  have hxr : x.re ∈ Icc R.x0 (R.x0 + R.w) := (DDDF.mem_toSet_iff.mp hx).1
  have hxi : x.im ∈ Icc R.y0 (R.y0 + R.h) := (DDDF.mem_toSet_iff.mp hx).2
  obtain ⟨a, ha, ha'⟩ := exists_rat_near_interval (by linarith : R.x0 < R.x0 + R.w)
    hxr (half_pos hρ)
  obtain ⟨b, hb, hb'⟩ := exists_rat_near_interval (by linarith : R.y0 < R.y0 + R.h)
    hxi (half_pos hρ)
  refine ⟨((a : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I,
    ⟨mk_mem_gaussRat a b, ?_⟩, (norm_mk_sub_le _ _ x).trans_lt (by linarith)⟩
  exact DDDF.mem_toSet_iff.mpr (by simpa using And.intro ha hb)

 
theorem gaussRat_vertical_side_dense (c : ℚ) {l u : ℝ}
    (hlu : l < u) (x : ℂ)
    (hx : x ∈ ({(c : ℝ)} ×ℂ Icc l u)) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ q ∈ gaussRat ∩ ({(c : ℝ)} ×ℂ Icc l u), ‖q - x‖ < ρ := by
  have hcoord : x.re = (c : ℝ) ∧ x.im ∈ Icc l u := by
    simpa only [Complex.mem_reProdIm, mem_singleton_iff] using hx
  obtain ⟨b, hb, hb'⟩ := exists_rat_near_interval hlu hcoord.2 hρ
  refine ⟨((c : ℝ) : ℂ) + ((b : ℝ) : ℂ) * Complex.I,
    ⟨mk_mem_gaussRat c b, ?_⟩, ?_⟩
  · simp only [Complex.mem_reProdIm, mem_singleton_iff,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      add_zero, Complex.add_im, Complex.mul_im, zero_add]
    exact ⟨trivial, hb⟩
  · apply (norm_mk_sub_le _ _ x).trans_lt
    rw [hcoord.1, sub_self, abs_zero, zero_add]
    exact hb'

 
theorem gaussRat_horizontal_side_dense (c : ℚ) {l u : ℝ}
    (hlu : l < u) (x : ℂ)
    (hx : x ∈ (Icc l u ×ℂ {(c : ℝ)})) (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ q ∈ gaussRat ∩ (Icc l u ×ℂ {(c : ℝ)}), ‖q - x‖ < ρ := by
  have hcoord : x.re ∈ Icc l u ∧ x.im = (c : ℝ) := by
    simpa only [Complex.mem_reProdIm, mem_singleton_iff] using hx
  obtain ⟨a, ha, ha'⟩ := exists_rat_near_interval hlu hcoord.1 hρ
  refine ⟨((a : ℝ) : ℂ) + ((c : ℝ) : ℂ) * Complex.I,
    ⟨mk_mem_gaussRat a c, ?_⟩, ?_⟩
  · simp only [Complex.mem_reProdIm, mem_singleton_iff,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
      add_zero, Complex.add_im, Complex.mul_im, zero_add]
    exact ⟨ha, trivial⟩
  · apply (norm_mk_sub_le _ _ x).trans_lt
    rw [hcoord.2, sub_self, abs_zero, add_zero]
    exact ha'

 

theorem small_segCost_of_compact {S : Set ℂ} (hS : IsCompact S)
    {ξ : ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    {η : ℝ} (hη : 0 < η) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ S, ∀ q : ℂ, ‖q - z‖ < ρ →
      segCost ξ f z q ≤ ENNReal.ofReal η := by
  let E : ℂ → ℝ := fun x => Real.exp (ξ * f x)
  have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul hf)
  have hK : IsCompact (Metric.cthickening 1 S) := hS.cthickening
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hE.continuousOn
  let ρ : ℝ := min 1 (η / (|M| + 1))
  have hρ : 0 < ρ := lt_min one_pos (by positivity)
  refine ⟨ρ, hρ, ?_⟩
  intro z hz q hq
  have hbound : ∀ x ∈ Metric.closedBall z ‖q - z‖, E x ≤ |M| := by
    intro x hx
    have hx' : x ∈ Metric.cthickening 1 S := by
      apply Metric.mem_cthickening_of_dist_le x z 1 S hz
      rw [Metric.mem_closedBall, dist_eq_norm] at hx
      rw [dist_eq_norm]
      exact hx.trans (hq.le.trans (min_le_left _ _))
    exact (le_abs_self (E x)).trans ((hM x hx').trans (le_abs_self M))
  have hρle : ρ ≤ η / (|M| + 1) := min_le_right _ _
  have hreal : |M| * ‖q - z‖ ≤ η := by
    have hq' : ‖q - z‖ ≤ η / (|M| + 1) := hq.le.trans hρle
    have hden : 0 < |M| + 1 := by positivity
    rw [le_div_iff₀ hden] at hq'
    nlinarith [abs_nonneg M, norm_nonneg (q - z)]
  exact (segCost_le hbound).trans (ENNReal.ofReal_le_ofReal hreal)




end SupercriticalLQGUniqueness.Exponent.PolygonalCost
