import LatticeProb.Prob.Cadlag.HalfLine.ZeroDistance
import LatticeProb.Prob.Cadlag.HalfLine.Triangle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Convergence of half-line path evaluations and averages

The integrated stopped discrepancy controls evaluation at continuity points.
Right continuity also recovers evaluations from shrinking right time averages.
-/

namespace LatticeProb.Cadlag.HalfLine

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

variable {E : Type*} [MetricSpace E]

/-- Vanishing half-line distance gives convergence at every continuity point of the limit. -/
theorem tendsto_eval_of_tendsto_skorohodDistance {x : ℕ → D E} {y : D E}
    (h : Tendsto (fun n => skorohodDistance (x n) y) atTop (𝓝 0))
    {t : Time} (ht : ContinuousAt y.1 t) :
    Tendsto (fun n => (x n).1 t) atTop (𝓝 (y.1 t)) := by
  classical
  have he : Tendsto (fun n => skorohodDistanceExtended (x n) y) atTop (𝓝 0) := by
    exact (ENNReal.tendsto_toReal_zero_iff (fun n =>
      ne_of_lt ((skorohodDistanceExtended_le_one (x n) y).trans_lt
        ENNReal.one_lt_top))).mp h
  have hp (n : ℕ) : ∃ l : Lambda,
      max (gamma l.1) (integratedDiscrepancy (x n) y l.1) <
        skorohodDistanceExtended (x n) y + ENNReal.ofReal (1 / (n + 1 : ℝ)) := by
    apply iInf_lt_iff.mp
    exact ENNReal.lt_add_right
      (ne_of_lt ((skorohodDistanceExtended_le_one _ _).trans_lt ENNReal.one_lt_top))
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  choose l hl using hp
  have hr : Tendsto (fun n : ℕ => skorohodDistanceExtended (x n) y +
      ENNReal.ofReal (1 / (n + 1 : ℝ))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, add_zero] using
      he.add (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat)
  have hg : Tendsto (fun n => gamma (l n).1) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
      (fun _ => bot_le) (fun n => (le_max_left _ _).trans (hl n).le)
  have hi : Tendsto (fun n => integratedDiscrepancy (x n) y (l n).1) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
      (fun _ => bot_le) (fun n => (le_max_right _ _).trans (hl n).le)
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  by_contra hbad
  have hfreq : ∃ᶠ n in atTop, ε ≤ dist ((x n).1 t) (y.1 t) := by
    simpa only [not_eventually, not_lt] using hbad
  obtain ⟨k, hk, hdist⟩ := extraction_of_frequently_atTop hfreq
  let f : ℕ → ℝ → ℝ≥0∞ := fun n u => ENNReal.ofReal (Real.exp (-u)) *
    discrepancy (x (k n)) y (l (k n)).1 u.toNNReal
  have hm (n : ℕ) : Measurable (f n) :=
    measurable_integratedDiscrepancy_integrand _ _ _
  have hz : (∫⁻ u : ℝ in Ioi 0, liminf (fun n => f n u) atTop) = 0 := by
    apply le_antisymm _ bot_le
    exact (lintegral_liminf_le hm).trans_eq (hi.comp hk.tendsto_atTop).liminf_eq
  have hae := (lintegral_eq_zero_iff (Measurable.liminf hm)).mp hz
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
  have htime := tendsto_timeChange_of_gamma (hg.comp hk.tendsto_atTop) t
  have hy := ht.tendsto.comp htime
  have hclose := (Metric.tendsto_nhds.mp hy) (ε / 2) (half_pos hε)
  have hb : ENNReal.ofReal (Real.exp (-u)) * min (ENNReal.ofReal (ε / 2)) 1 ≤
      liminf (fun n => f n u) atTop := by
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hclose, htime.eventually (Iio_mem_nhds htu')] with n hn hstop
    apply mul_le_mul_right
    have hd : ε / 2 ≤ dist ((x (k n)).1 t) (y.1 ((l (k n)).1 t)) := by
      have htri := dist_triangle ((x (k n)).1 t) (y.1 ((l (k n)).1 t)) (y.1 t)
      dsimp only [Function.comp_def] at hn
      linarith [hdist n]
    have hq : min (ENNReal.ofReal (ε / 2)) 1 ≤
        q ((x (k n)).1 t) (y.1 ((l (k n)).1 t)) := by
      exact min_le_min_right 1 (by simpa only [edist_dist] using ENNReal.ofReal_le_ofReal hd)
    have hs := le_iSup (fun s : Time => q ((x (k n)).1 (min s u.toNNReal))
      (y.1 (min ((l (k n)).1 s) u.toNNReal))) t
    exact hq.trans (by
      simpa only [discrepancy, min_eq_left htu'.le, min_eq_left hstop.le] using hs)
  change liminf (fun n => f n u) atTop = 0 at hu
  rw [hu] at hb
  have hzero := (mul_eq_zero.mp (le_antisymm hb bot_le)).resolve_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
  exact (ne_of_gt (lt_min (ENNReal.ofReal_pos.mpr (half_pos hε)) zero_lt_one)) hzero

/-- Fixed positive time averages of bounded continuous observables converge with the paths. -/
theorem tendsto_average_of_tendsto_skorohodDistance {x : ℕ → D E} {y : D E}
    (h : Tendsto (fun n => skorohodDistance (x n) y) atTop (𝓝 0))
    {f : E → ℝ} (hf : Continuous f) (hb : ∃ M : ℝ, ∀ a, ‖f a‖ ≤ M)
    (t : Time) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => (1 / ε) *
      ∫ s in (t : ℝ)..(t : ℝ) + ε, f ((x n).1 s.toNNReal)) atTop
      (𝓝 ((1 / ε) * ∫ s in (t : ℝ)..(t : ℝ) + ε, f (y.1 s.toNNReal))) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  obtain ⟨M, hM⟩ := hb
  have hm (n : ℕ) : Measurable (fun s : ℝ => f ((x n).1 s.toNNReal)) :=
    hf.measurable.comp ((measurable_isCadlag (x n).2).comp
      continuous_real_toNNReal.measurable)
  have hae := (y.2.countable_discontinuities.image (fun s : Time => (s : ℝ))).ae_notMem
    volume
  have hi : Tendsto (fun n => ∫ s in Ioc (t : ℝ) ((t : ℝ) + ε),
      f ((x n).1 s.toNNReal)) atTop
      (𝓝 (∫ s in Ioc (t : ℝ) ((t : ℝ) + ε), f (y.1 s.toNNReal))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => M)
    · intro n
      exact (hm n).aestronglyMeasurable.restrict
    · exact integrable_const M
    · intro n
      exact Eventually.of_forall fun s => hM _
    · filter_upwards [hae.filter_mono (ae_mono Measure.restrict_le_self),
        ae_restrict_mem measurableSet_Ioc] with s hs hst
      have hspos : 0 ≤ s := t.2.trans hst.1.le
      have hc : ContinuousAt y.1 s.toNNReal := by
        by_contra hnot
        exact hs ⟨s.toNNReal, hnot, Real.coe_toNNReal s hspos⟩
      exact hf.continuousAt.tendsto.comp
        (tendsto_eval_of_tendsto_skorohodDistance h hc)
  have hle : (t : ℝ) ≤ (t : ℝ) + ε := le_add_of_nonneg_right hε.le
  simpa only [intervalIntegral.integral_of_le hle] using hi.const_mul (1 / ε)

/-- Right time averages of a continuous observable recover its càdlàg evaluation. -/
theorem tendsto_average_eval (y : D E) {f : E → ℝ} (hf : Continuous f) (t : Time) :
    Tendsto (fun ε : ℝ => (1 / ε) *
      ∫ s in (t : ℝ)..(t : ℝ) + ε, f (y.1 s.toNNReal))
      (𝓝[>] 0) (𝓝 (f (y.1 t))) := by
  letI : MeasurableSpace E := borel E
  letI : BorelSpace E := ⟨rfl⟩
  let g : ℝ → ℝ := fun s => f (y.1 s.toNNReal)
  have hm : Measurable g :=
    hf.measurable.comp ((measurable_isCadlag y.2).comp
      continuous_real_toNNReal.measurable)
  have hc : ContinuousWithinAt g (Ici (t : ℝ)) (t : ℝ) := by
    have htime : ContinuousWithinAt Real.toNNReal (Ici (t : ℝ)) (t : ℝ) :=
      continuous_real_toNNReal.continuousWithinAt
    have hpath := (y.2.1 t).comp_of_eq htime (fun s hs => by
      change t ≤ s.toNNReal
      exact_mod_cast (show (t : ℝ) ≤ (s.toNNReal : ℝ) from
        hs.trans (Real.le_coe_toNNReal s))) (Real.toNNReal_coe)
    exact hf.continuousAt.comp_continuousWithinAt hpath
  have hd : HasDerivWithinAt (fun u => ∫ s in (t : ℝ)..u, g s)
      (g t) (Ici (t : ℝ)) (t : ℝ) :=
    intervalIntegral.integral_hasDerivWithinAt_right
      (IntervalIntegrable.refl) hm.stronglyMeasurable.stronglyMeasurableAtFilter
      (hc.mono Ioi_subset_Ici_self)
  have hs := hasDerivWithinAt_iff_tendsto_slope.mp hd
  have hshift : Tendsto (fun ε : ℝ => (t : ℝ) + ε) (𝓝[>] 0) (𝓝[>] (t : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [add_zero, id_eq] using
        (tendsto_const_nhds.add (tendsto_id.mono_left nhdsWithin_le_nhds :
          Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0)))
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change (t : ℝ) < (t : ℝ) + ε
      exact lt_add_of_pos_right _ (show 0 < ε from hε)
  have hsub : Ioi (t : ℝ) ⊆ Ici (t : ℝ) \ {(t : ℝ)} := by
    intro s hs
    exact ⟨le_of_lt (show (t : ℝ) < s from hs), ne_of_gt hs⟩
  have hlim := (hs.mono_left (nhdsWithin_mono _ hsub)).comp hshift
  simpa only [Function.comp_def, slope_def_field, intervalIntegral.integral_same, sub_zero,
    add_sub_cancel_left, div_eq_inv_mul, one_div, mul_one, g, Real.toNNReal_coe] using hlim

end LatticeProb.Cadlag.HalfLine
