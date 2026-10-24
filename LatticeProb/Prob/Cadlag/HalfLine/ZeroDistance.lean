import LatticeProb.Prob.Cadlag.HalfLine.Discrepancy
import LatticeProb.Prob.Cadlag.HalfLine.TimeChange
import LatticeProb.Prob.Cadlag.HalfLine.Paths

/-!
# Separation for the half-line Skorokhod distance

Vanishing distortion forces time changes to converge to the identity. Fatou's lemma
then detects agreement at every continuity point, and right continuity gives equality.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {E : Type*} [MetricSpace E]

/-- Distortions tending to zero force pointwise convergence to the identity time change. -/
theorem tendsto_timeChange_of_gamma {l : ℕ → Lambda}
    (h : Tendsto (fun n => gamma (l n).1) atTop (𝓝 0)) (t : Time) :
    Tendsto (fun n => (l n).1 t) atTop (𝓝 t) := by
  apply NNReal.tendsto_coe.mp
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hg := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have hb : Tendsto (fun n => (t : ℝ) * (Real.exp (gamma (l n).1).toReal - 1))
      atTop (𝓝 0) := by
    have he : Tendsto (fun n => Real.exp (gamma (l n).1).toReal - 1)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, ENNReal.toReal_zero, Real.exp_zero, sub_self] using
        ((Real.continuous_exp.continuousAt.tendsto.comp hg).sub_const 1)
    simpa only [mul_zero] using he.const_mul (t : ℝ)
  exact squeeze_zero (fun n => dist_nonneg)
    (fun n => abs_sub_le_of_gamma (l n).1 (ne_of_lt (l n).2.2) t) hb

/-- Zero extended Skorokhod distance separates genuine half-line càdlàg paths. -/
theorem eq_of_skorohodDistanceExtended_eq_zero {x y : D E}
    (h : skorohodDistanceExtended x y = 0) : x = y := by
  classical
  have hp (n : ℕ) : ∃ l : Lambda,
      max (gamma l.1) (integratedDiscrepancy x y l.1) <
        ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    apply iInf_lt_iff.mp
    rw [← skorohodDistanceExtended, h]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  choose l hl using hp
  have hr : Tendsto (fun n : ℕ => ENNReal.ofReal (1 / (n + 1 : ℝ)))
      atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat
  have hg : Tendsto (fun n => gamma (l n).1) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
      (fun _ => bot_le) (fun n => (le_max_left _ _).trans (hl n).le)
  have hi : Tendsto (fun n => integratedDiscrepancy x y (l n).1) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
      (fun _ => bot_le) (fun n => (le_max_right _ _).trans (hl n).le)
  let f : ℕ → ℝ → ℝ≥0∞ := fun n u =>
    ENNReal.ofReal (Real.exp (-u)) * discrepancy x y (l n).1 u.toNNReal
  have hm (n : ℕ) : Measurable (f n) :=
    measurable_integratedDiscrepancy_integrand x y (l n).1
  have hz : (∫⁻ u : ℝ in Ioi 0, liminf (fun n => f n u) atTop) = 0 := by
    apply le_antisymm _ bot_le
    exact (lintegral_liminf_le hm).trans_eq hi.liminf_eq
  have hae : ∀ᵐ u : ℝ ∂volume.restrict (Ioi 0),
      liminf (fun n => f n u) atTop = 0 :=
    (lintegral_eq_zero_iff (Measurable.liminf hm)).mp hz
  apply Subtype.ext
  apply x.2.eq_of_eqOn_dense y.2 y.2.dense_continuity_points
  intro t ht
  have htail : volume.restrict (Ioi (0 : ℝ)) (Ioi (t : ℝ)) ≠ 0 := by
    have hs : Ioi (t : ℝ) ⊆ Ioi (0 : ℝ) := fun u hu => t.2.trans_lt hu
    rw [Measure.restrict_apply measurableSet_Ioi, inter_eq_left.mpr hs,
      Real.volume_Ioi]
    exact ENNReal.top_ne_zero
  obtain ⟨u, htu, hu⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae htail
    (hae.filter_mono (ae_mono (Measure.restrict_le_self)))
  have htu' : t < u.toNNReal := by
    exact_mod_cast (show (t : ℝ) < (u.toNNReal : ℝ) by
      rw [Real.coe_toNNReal _ (t.2.trans htu.le)]
      exact htu)
  have htime := tendsto_timeChange_of_gamma hg t
  have hy : Tendsto (fun n => y.1 ((l n).1 t)) atTop (𝓝 (y.1 t)) := ht.tendsto.comp htime
  have hq : Tendsto (fun n => q (x.1 t) (y.1 ((l n).1 t)))
      atTop (𝓝 (q (x.1 t) (y.1 t))) :=
    (tendsto_const_nhds.edist hy).min tendsto_const_nhds
  have hw : Tendsto (fun n => ENNReal.ofReal (Real.exp (-u)) *
      q (x.1 t) (y.1 ((l n).1 t))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (-u)) * q (x.1 t) (y.1 t))) :=
    ENNReal.Tendsto.const_mul hq (Or.inr ENNReal.ofReal_ne_top)
  have hbound : ENNReal.ofReal (Real.exp (-u)) * q (x.1 t) (y.1 t) ≤
      liminf (fun n => f n u) atTop := by
    rw [← hw.liminf_eq]
    refine liminf_le_liminf ?_
    filter_upwards [htime.eventually (Iio_mem_nhds htu')] with n hn
    apply mul_le_mul_right
    have hb := le_iSup (fun s : Time =>
      q (x.1 (min s u.toNNReal)) (y.1 (min ((l n).1 s) u.toNNReal))) t
    simpa only [discrepancy, min_eq_left htu'.le, min_eq_left hn.le] using hb
  rw [hu] at hbound
  have hzero := (mul_eq_zero.mp (le_antisymm hbound bot_le)).resolve_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
  have he : edist (x.1 t) (y.1 t) = 0 := by
    exact (min_eq_zero.mp hzero).resolve_right (by norm_num)
  exact edist_eq_zero.mp he

/-- The finite real-valued Skorokhod distance also separates paths. -/
theorem eq_of_skorohodDistance_eq_zero {x y : D E}
    (h : skorohodDistance x y = 0) : x = y := by
  apply eq_of_skorohodDistanceExtended_eq_zero
  exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right
    (ne_of_lt ((skorohodDistanceExtended_le_one x y).trans_lt ENNReal.one_lt_top))

end LatticeProb.Cadlag.HalfLine
