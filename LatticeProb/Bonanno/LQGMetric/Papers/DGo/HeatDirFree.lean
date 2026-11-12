/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirFree at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirTime
import LatticeProb.Bonanno.LQGMetric.Field.WhiteNoiseKernel

/-!
# DGo (3.1): the circle-averaged free heat kernel is in `L²` (task P2-HEAT1, packet R0)

Ding–Goswami, arXiv:1610.09998, (3.1) (DGo:491–494). For `δ > 0`, `T > 0` the function
`G(s, z) = 1_{(0,T]}(s) (2π)⁻¹ ∫_{(0,2π]} p_{s/2}(v + δe^{iθ}, z) dθ` is in `L²(ℝ × ℂ)`
(`memLp_freeCircFun`). Proof (Tonelli): `∫∫ G² = (2π)⁻² ∫∫ dθ dθ' ∫_0^T p_s(x_θ, x_θ') ds`
(Gaussian Chapman–Kolmogorov `integral_heatKernel_mul_heatKernel`), and
`∫_0^T p_s(x,y) ds ≤ C(1 + |log|x−y||)` (`HeatDir.lintegral_heatKernel_time_le`) is integrable on the
circle (`HeatDir.integral_abs_log_circle_le`). This is the circle-average form of DGo
(eq:Green_fxn) (DGo:479–486); own elementary write-up (proposed DEVIATIONS HEAT1-1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Real Set Function
open scoped ENNReal Interval

namespace LQGMetric
namespace DGo
namespace HeatDir

variable {T δ : ℝ} {v : ℂ}

/-- `p_{s/2}(v + δe^{iθ}, z)` at `q = (s, z)` -/
def circHeat (δ : ℝ) (v : ℂ) (q : ℝ × ℂ) (θ : ℝ) : ℝ :=
  heatKernel (q.1 / 2) (circleMap v δ θ) q.2

lemma measurable_circHeat : Measurable (uncurry (circHeat δ v)) := by
  have hc : Measurable fun p : (ℝ × ℂ) × ℝ => circleMap v δ p.2 :=
    (continuous_circleMap v δ).measurable.comp measurable_snd
  have h1 : Measurable fun p : (ℝ × ℂ) × ℝ => p.1.1 := measurable_fst.comp measurable_fst
  have h2 : Measurable fun p : (ℝ × ℂ) × ℝ => p.1.2 := measurable_snd.comp measurable_fst
  change Measurable fun p : (ℝ × ℂ) × ℝ => heatKernel (p.1.1 / 2) (circleMap v δ p.2) p.1.2
  unfold heatKernel
  exact ((measurable_const.mul (h1.div_const 2)).inv).mul (Real.measurable_exp.comp
    ((((hc.sub h2).norm.pow_const 2).neg).div (measurable_const.mul (h1.div_const 2))))

lemma continuous_circHeat (q : ℝ × ℂ) : Continuous (circHeat δ v q) := by
  have hc := continuous_circleMap v δ
  unfold circHeat heatKernel
  fun_prop

lemma circHeat_nonneg {q : ℝ × ℂ} (hq : 0 < q.1) (θ : ℝ) : 0 ≤ circHeat δ v q θ :=
  heatKernel_nonneg _ (by linarith) _ _

lemma integrableOn_circHeat (q : ℝ × ℂ) : IntegrableOn (circHeat δ v q) (Ioc 0 (2 * π)) :=
  ((continuous_circHeat q).integrableOn_Icc).mono_set Ioc_subset_Icc_self

/-- the circle average of the free kernel, cut to `s ∈ (0, T]` -/
def freeCircFun (T δ : ℝ) (v : ℂ) (q : ℝ × ℂ) : ℝ :=
  (Ioc 0 T ×ˢ univ).indicator (fun q => (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), circHeat δ v q θ) q

lemma measurable_freeCircFun : Measurable (freeCircFun T δ v) := by
  have h := (measurable_circHeat (δ := δ) (v := v)).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioc 0 (2 * π)))
  exact (h.measurable.const_mul _).indicator (measurableSet_Ioc.prod MeasurableSet.univ)

lemma freeCircFun_nonneg (q : ℝ × ℂ) : 0 ≤ freeCircFun T δ v q := by
  unfold freeCircFun
  refine indicator_nonneg (fun q hq => ?_) q
  exact mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioc fun θ _ =>
    circHeat_nonneg hq.1.1 θ)

/-- `ofReal (G²)` as a double `θ`-lintegral -/
lemma ofReal_freeCircFun_sq (q : ℝ × ℂ) :
    ENNReal.ofReal (freeCircFun T δ v q ^ 2) = (Ioc 0 T ×ˢ univ).indicator (fun q =>
      ENNReal.ofReal ((2 * π)⁻¹) ^ 2 * ∫⁻ θ in Ioc 0 (2 * π), ∫⁻ θ' in Ioc 0 (2 * π),
        ENNReal.ofReal (circHeat δ v q θ) * ENNReal.ofReal (circHeat δ v q θ')) q := by
  by_cases hq : q ∈ Ioc 0 T ×ˢ (univ : Set ℂ)
  · rw [indicator_of_mem hq]
    unfold freeCircFun
    rw [indicator_of_mem hq]
    have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 (2 * π))] circHeat δ v q :=
      ae_restrict_of_forall_mem measurableSet_Ioc fun θ _ => circHeat_nonneg hq.1.1 θ
    have hm : AEMeasurable (fun θ => ENNReal.ofReal (circHeat δ v q θ))
        ((volume : Measure ℝ).restrict (Ioc 0 (2 * π))) :=
      (ENNReal.measurable_ofReal.comp (continuous_circHeat q).measurable).aemeasurable
    rw [lintegral_lintegral_mul hm hm, ENNReal.ofReal_pow (mul_nonneg (by positivity)
      (integral_nonneg_of_ae hnn)), ENNReal.ofReal_mul (by positivity),
      ofReal_integral_eq_lintegral_ofReal (integrableOn_circHeat q) hnn]
    ring
  · rw [indicator_of_notMem hq]
    unfold freeCircFun
    rw [indicator_of_notMem hq]; simp

/-- the `z`-integral: `∫ p_{s/2}(x,z) p_{s/2}(x',z) dz = p_s(x,x')` in `ℝ≥0∞` -/
lemma lintegral_heat_mul_heat {s : ℝ} (hs : 0 < s) (x x' : ℂ) :
    ∫⁻ z, ENNReal.ofReal (heatKernel (s / 2) x z) * ENNReal.ofReal (heatKernel (s / 2) x' z) =
      ENNReal.ofReal (heatKernel s x x') := by
  have h2 : 0 < s / 2 := half_pos hs
  simp_rw [← ENNReal.ofReal_mul (heatKernel_nonneg _ h2.le _ _)]
  rw [← ofReal_integral_eq_lintegral_ofReal (WhiteNoise.integrable_heatKernel_mul_heatKernel _ h2 x x')
    (Filter.Eventually.of_forall fun z => mul_nonneg (heatKernel_nonneg _ h2.le _ _)
      (heatKernel_nonneg _ h2.le _ _)), WhiteNoise.integral_heatKernel_mul_heatKernel _ h2,
    mul_div_cancel₀ _ (two_ne_zero)]

/-- the `θ'`-integral of the time bound, uniformly in `θ` -/
lemma lintegral_circle_time_le (hδ : 0 < δ) (θ : ℝ) :
    ∫⁻ θ' in Ioc 0 (2 * π), ∫⁻ s in Ioc 0 T,
        ENNReal.ofReal (heatKernel s (circleMap v δ θ) (circleMap v δ θ')) ≤
      ENNReal.ofReal (2 + |Real.log T| + 2 * (2 * log⁺ (2 * δ) - Real.log δ)) := by
  set x := circleMap v δ θ
  set B : ℝ → ℝ := fun θ' =>
    1 / π + (2 * π)⁻¹ * (|Real.log T| + 2 * |Real.log ‖circleMap v δ θ' - x‖|)
  have hcount : (range fun n : ℤ => θ + n * (2 * π)).Countable := countable_range _
  have hae : ∀ᵐ θ' ∂(volume : Measure ℝ).restrict (Ioc 0 (2 * π)), circleMap v δ θ' ≠ x := by
    refine ae_restrict_of_ae ((hcount.ae_notMem volume).mono fun θ' h heq => h ?_)
    obtain ⟨n, hn⟩ := (circleMap_eq_circleMap_iff v hδ.ne').1 heq
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hI : IntervalIntegrable (fun θ' => Real.log ‖circleMap v δ θ' - x‖) volume 0 (2 * π) :=
    circleIntegrable_log_norm_sub_const (a := x) (c := v) δ
  have hBi : IntegrableOn B (Ioc 0 (2 * π)) := by
    have : IntervalIntegrable B volume 0 (2 * π) :=
      intervalIntegrable_const.add ((intervalIntegrable_const.add (hI.abs.const_mul 2)).const_mul _)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 this
  have hB0 : ∀ θ', 0 ≤ B θ' := fun θ' => by positivity
  calc ∫⁻ θ' in Ioc 0 (2 * π), ∫⁻ s in Ioc 0 T,
        ENNReal.ofReal (heatKernel s x (circleMap v δ θ'))
      ≤ ∫⁻ θ' in Ioc 0 (2 * π), ENNReal.ofReal (B θ') := by
        refine lintegral_mono_ae (hae.mono fun θ' hne => ?_)
        have hr : 0 < ‖x - circleMap v δ θ'‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
        have := lintegral_heatKernel_time_le T hr
        rwa [norm_sub_rev] at this
    _ = ENNReal.ofReal (∫ θ' in Ioc 0 (2 * π), B θ') :=
        (ofReal_integral_eq_lintegral_ofReal hBi (Filter.Eventually.of_forall hB0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← intervalIntegral.integral_of_le (by positivity)]
        have hlog := integral_abs_log_circle_le hδ v x
        have hvx : ‖v - x‖ = δ := by
          rw [norm_sub_rev, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hδ]
        rw [hvx, show δ + δ = 2 * δ by ring] at hlog
        simp only [B]
        rw [intervalIntegral.integral_add intervalIntegrable_const
            ((intervalIntegrable_const.add (hI.abs.const_mul 2)).const_mul _),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_add intervalIntegrable_const (hI.abs.const_mul 2),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        simp only [sub_zero, smul_eq_mul]
        have hπ : 0 < π := Real.pi_pos
        have e1 : 2 * π * (1 / π) = 2 := by field_simp
        have e2 : (2 * π)⁻¹ * (2 * π * |Real.log T| + 2 * ∫ θ' in (0 : ℝ)..2 * π,
            |Real.log ‖circleMap v δ θ' - x‖|) = |Real.log T| + (2 * π)⁻¹ * 2 *
              ∫ θ' in (0 : ℝ)..2 * π, |Real.log ‖circleMap v δ θ' - x‖| := by
          field_simp
        rw [e1, e2]
        have e3 : (2 * π)⁻¹ * 2 * (2 * π * (2 * log⁺ (2 * δ) - Real.log δ)) =
            2 * (2 * log⁺ (2 * δ) - Real.log δ) := by field_simp
        have := mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹ * 2)
        linarith

/-- **The circle-averaged free heat kernel is in `L²(ℝ × ℂ)`** (`δ > 0`). -/
theorem memLp_freeCircFun (hδ : 0 < δ) (T : ℝ) (v : ℂ) :
    MemLp (freeCircFun T δ v) 2 (volume : Measure (ℝ × ℂ)) := by
  have hm := (measurable_freeCircFun (T := T) (δ := δ) (v := v)).aestronglyMeasurable
    (μ := (volume : Measure (ℝ × ℂ)))
  refine (memLp_two_iff_integrable_sq hm).2 ⟨hm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun q => by positivity)]
  set I := Ioc (0 : ℝ) (2 * π)
  set S := Ioc 0 T ×ˢ (univ : Set ℂ)
  set k : (ℝ × ℂ) → ℝ → ℝ → ℝ≥0∞ := fun q θ θ' =>
    ENNReal.ofReal (circHeat δ v q θ) * ENNReal.ofReal (circHeat δ v q θ')
  have hk : Measurable fun p : ((ℝ × ℂ) × ℝ) × ℝ => k p.1.1 p.1.2 p.2 := by
    have hc := measurable_circHeat (δ := δ) (v := v)
    exact (ENNReal.measurable_ofReal.comp (hc.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp (hc.comp ((measurable_fst.comp measurable_fst).prodMk
        measurable_snd)))
  have hk1 : Measurable fun p : (ℝ × ℂ) × ℝ => ∫⁻ θ' in I, k p.1 p.2 θ' :=
    hk.lintegral_prod_right'
  simp_rw [ofReal_freeCircFun_sq]
  rw [lintegral_indicator (measurableSet_Ioc.prod MeasurableSet.univ),
    lintegral_const_mul' _ _ (by simp)]
  refine ENNReal.mul_lt_top (by simp) ?_
  rw [lintegral_lintegral_swap hk1.aemeasurable]
  have hstep : ∀ θ, ∫⁻ q in S, ∫⁻ θ' in I, k q θ θ' =
      ∫⁻ θ' in I, ∫⁻ s in Ioc 0 T,
        ENNReal.ofReal (heatKernel s (circleMap v δ θ) (circleMap v δ θ')) := by
    intro θ
    have hk2 : Measurable fun p : (ℝ × ℂ) × ℝ => k p.1 θ p.2 :=
      hk.comp (f := fun p : (ℝ × ℂ) × ℝ => ((p.1, θ), p.2))
        ((measurable_fst.prodMk measurable_const).prodMk measurable_snd)
    rw [lintegral_lintegral_swap hk2.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioc fun θ' _ => ?_
    have hk3 : Measurable fun q : ℝ × ℂ => k q θ θ' :=
      hk.comp (f := fun q : ℝ × ℂ => ((q, θ), θ'))
        ((measurable_id.prodMk measurable_const).prodMk measurable_const)
    rw [show S = Ioc 0 T ×ˢ univ from rfl, Measure.volume_eq_prod, ← Measure.prod_restrict,
      Measure.restrict_univ, lintegral_prod _ hk3.aemeasurable]
    refine setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    exact lintegral_heat_mul_heat hs.1 _ _
  refine (lintegral_congr fun θ => hstep θ).trans_lt ?_
  calc ∫⁻ θ in I, ∫⁻ θ' in I, ∫⁻ s in Ioc 0 T,
        ENNReal.ofReal (heatKernel s (circleMap v δ θ) (circleMap v δ θ'))
      ≤ ∫⁻ _ in I, ENNReal.ofReal (2 + |Real.log T| + 2 * (2 * log⁺ (2 * δ) - Real.log δ)) :=
        lintegral_mono fun θ => lintegral_circle_time_le hδ θ
    _ < ⊤ := by
        rw [setLIntegral_const, Real.volume_Ioc]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

end HeatDir
end DGo
end LQGMetric
