/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DGo.HeatDirR2a at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.HeatDirFree
import LatticeProb.Bonanno.LQGMetric.Papers.DGo.CircleKernel
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6P29KerFn

/-!
# DGo (3.10), the free parts `G_{v;2}` and `G_{v;4}` in function form (task P2-HEAT2, packet R2)

Ding–Goswami, arXiv:1610.09998, `Watabiki_final.tex`, proof of Prop 3.3 (DGo:618–700).

* `lintegral_heatKernel_time_le_sq` — `∫_0^{δ²} p_s(x,y) ds ≤ 1/π + (2π)⁻¹ · 2 log(2δ/|x−y|)` for
  `0 < |x−y| ≤ 2δ` (the sharp form of `lintegral_heatKernel_time_le`).
* `lintegral_circle_time_le_sq` — its `θ'`-average over `∂B_δ(v)` is `≤ 2 + 2 log 2`, uniformly in
  `δ` (Jensen's formula: the circle average of `log|· − x|` over a circle through `x` is `log δ`).
* `lintegral_freeCircFun_sq_le` — **`G_{v;2}`** (DGo:661–668): the circle-averaged free kernel cut
  at `s ≤ δ²` has `L²` norm `≤ (2π)⁻¹(2 + 2 log 2)`, uniformly in `δ`, `v`. DGo bound the
  `θ`-integral by `O(√s/δ)` (DGo:668); we integrate in `s` first and use Jensen's formula
  instead (own elementary variant, proposed DEVIATIONS HEAT2-1).
* `lintegral_g4Fun_sq_le` — **`G_{v;4}`** (DGo:684–700) in function form: `∫∫ g₄² ≤ 1/π` for
  `g₄ = 1_{[δ²,1]}(s)((2π)⁻¹∫ p_{s/2}(v+δe^{iθ}, z) dθ − p_{s/2}(v, z))`, from Cauchy–Schwarz in `θ`
  and DGo Lemma 3.2 (`norm_sqrtPi_smul_phiKernelL2_sub_le`), as in `dgo_varG4_le`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Real Set Function
open scoped ENNReal Interval

namespace LQGMetric
namespace DGo
namespace HeatDir

variable {δ : ℝ} {v : ℂ}

/-- **Sharp time integral**: `∫_0^{δ²} p_s(x,y) ds ≤ 1/π + (2π)⁻¹(2 log 2 + 2 log δ − 2 log|x−y|)`
for `0 < |x − y| ≤ 2δ`. -/
theorem lintegral_heatKernel_time_le_sq (hδ : 0 < δ) {x y : ℂ} (hr : 0 < ‖x - y‖)
    (hr2 : ‖x - y‖ ≤ 2 * δ) :
    ∫⁻ s in Ioc 0 (δ ^ 2), ENNReal.ofReal (heatKernel s x y) ≤
      ENNReal.ofReal (1 / π + (2 * π)⁻¹ *
        (2 * Real.log 2 + 2 * Real.log δ - 2 * Real.log ‖x - y‖)) := by
  set r := ‖x - y‖
  have hr2' : 0 < r ^ 2 := by positivity
  set M := max (δ ^ 2) (r ^ 2)
  have hM : r ^ 2 ≤ M := le_max_right _ _
  have hM4 : M ≤ 4 * δ ^ 2 := max_le (by nlinarith) (by nlinarith)
  have hlogr : Real.log r ≤ Real.log 2 + Real.log δ := by
    rw [← Real.log_mul (by norm_num) hδ.ne']; exact Real.log_le_log hr hr2
  have hsub : Ioc 0 (δ ^ 2) ⊆ Ioc 0 (r ^ 2) ∪ Ioc (r ^ 2) M := by
    rw [Ioc_union_Ioc_eq_Ioc hr2'.le hM]; exact Ioc_subset_Ioc_right (le_max_left _ _)
  have h1 : ∫⁻ s in Ioc 0 (r ^ 2), ENNReal.ofReal (heatKernel s x y) ≤ ENNReal.ofReal (1 / π) := by
    calc ∫⁻ s in Ioc 0 (r ^ 2), ENNReal.ofReal (heatKernel s x y)
        ≤ ∫⁻ _ in Ioc 0 (r ^ 2), ENNReal.ofReal ((π * r ^ 2)⁻¹) :=
          setLIntegral_mono measurable_const fun s hs =>
            ENNReal.ofReal_le_ofReal (heatKernel_le_inv_sq hs.1 hr)
      _ = ENNReal.ofReal (1 / π) := by
          rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← ENNReal.ofReal_mul (by positivity)]
          congr 1; field_simp
  have hint : IntegrableOn (fun s : ℝ => (2 * π)⁻¹ * s⁻¹) (Ioc (r ^ 2) M) := by
    have : IntervalIntegrable (fun s : ℝ => (2 * π)⁻¹ * s⁻¹) volume (r ^ 2) M :=
      (intervalIntegral.intervalIntegrable_inv (fun s hs => by
        rw [Set.uIcc_of_le hM] at hs; exact (hr2'.trans_le hs.1).ne') continuousOn_id
        |>.const_mul _)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hM).1 this
  have h2 : ∫⁻ s in Ioc (r ^ 2) M, ENNReal.ofReal (heatKernel s x y) ≤
      ENNReal.ofReal ((2 * π)⁻¹ * (2 * Real.log 2 + 2 * Real.log δ - 2 * Real.log r)) := by
    calc ∫⁻ s in Ioc (r ^ 2) M, ENNReal.ofReal (heatKernel s x y)
        ≤ ∫⁻ s in Ioc (r ^ 2) M, ENNReal.ofReal ((2 * π)⁻¹ * s⁻¹) :=
          setLIntegral_mono' measurableSet_Ioc fun s hs =>
            ENNReal.ofReal_le_ofReal (heatKernel_le_inv_time (hr2'.trans hs.1) x y)
      _ = ENNReal.ofReal (∫ s in Ioc (r ^ 2) M, (2 * π)⁻¹ * s⁻¹) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs =>
              by have := hr2'.trans hs.1; positivity)).symm
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← intervalIntegral.integral_of_le hM, intervalIntegral.integral_const_mul,
            integral_inv_of_pos hr2' (hr2'.trans_le hM)]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [Real.log_div (hr2'.trans_le hM).ne' hr2'.ne', Real.log_pow]
          have hlM : Real.log M ≤ 2 * Real.log 2 + 2 * Real.log δ := by
            have : Real.log (4 * δ ^ 2) = 2 * Real.log 2 + 2 * Real.log δ := by
              rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow,
                show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
              push_cast; ring
            rw [← this]
            exact Real.log_le_log (hr2'.trans_le hM) hM4
          push_cast
          linarith
  have hnn : 0 ≤ (2 * π)⁻¹ * (2 * Real.log 2 + 2 * Real.log δ - 2 * Real.log r) :=
    mul_nonneg (by positivity) (by linarith)
  calc ∫⁻ s in Ioc 0 (δ ^ 2), ENNReal.ofReal (heatKernel s x y)
      ≤ ∫⁻ s in Ioc 0 (r ^ 2) ∪ Ioc (r ^ 2) M, ENNReal.ofReal (heatKernel s x y) :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ s in Ioc 0 (r ^ 2), ENNReal.ofReal (heatKernel s x y)) +
          ∫⁻ s in Ioc (r ^ 2) M, ENNReal.ofReal (heatKernel s x y) := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal (1 / π) +
          ENNReal.ofReal ((2 * π)⁻¹ * (2 * Real.log 2 + 2 * Real.log δ - 2 * Real.log r)) :=
        add_le_add h1 h2
    _ = _ := (ENNReal.ofReal_add (by positivity) hnn).symm

/-- the `θ'`-average of the sharp time bound over a circle through the base point -/
lemma lintegral_circle_time_le_sq (hδ : 0 < δ) (v : ℂ) (θ : ℝ) :
    ∫⁻ θ' in Ioc 0 (2 * π), ∫⁻ s in Ioc 0 (δ ^ 2),
        ENNReal.ofReal (heatKernel s (circleMap v δ θ) (circleMap v δ θ')) ≤
      ENNReal.ofReal (2 + 2 * Real.log 2) := by
  set x := circleMap v δ θ
  set B : ℝ → ℝ := fun θ' => 1 / π + (2 * π)⁻¹ *
    (2 * Real.log 2 + 2 * Real.log δ - 2 * Real.log ‖circleMap v δ θ' - x‖)
  have hcount : (range fun n : ℤ => θ + n * (2 * π)).Countable := countable_range _
  have hae : ∀ᵐ θ' ∂(volume : Measure ℝ).restrict (Ioc 0 (2 * π)), circleMap v δ θ' ≠ x := by
    refine ae_restrict_of_ae ((hcount.ae_notMem volume).mono fun θ' h heq => h ?_)
    obtain ⟨n, hn⟩ := (circleMap_eq_circleMap_iff v hδ.ne').1 heq
    refine ⟨n, ?_⟩
    have := congrArg Complex.im hn
    simp at this
    linarith
  have hle2 : ∀ θ', ‖circleMap v δ θ' - x‖ ≤ 2 * δ := fun θ' => by
    calc ‖circleMap v δ θ' - x‖ = ‖(circleMap v δ θ' - v) - (x - v)‖ := by ring_nf
      _ ≤ ‖circleMap v δ θ' - v‖ + ‖x - v‖ := norm_sub_le _ _
      _ = 2 * δ := by
          simp only [x, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hδ]; ring
  have hI : IntervalIntegrable (fun θ' => Real.log ‖circleMap v δ θ' - x‖) volume 0 (2 * π) :=
    circleIntegrable_log_norm_sub_const (a := x) (c := v) δ
  have hBi : IntegrableOn B (Ioc 0 (2 * π)) := by
    have : IntervalIntegrable B volume 0 (2 * π) :=
      intervalIntegrable_const.add ((intervalIntegrable_const.sub (hI.const_mul 2)).const_mul _)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 this
  have hB0 : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc 0 (2 * π))] B := by
    filter_upwards [hae] with θ' hne
    have hr : 0 < ‖circleMap v δ θ' - x‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have hlogr : Real.log ‖circleMap v δ θ' - x‖ ≤ Real.log 2 + Real.log δ := by
      rw [← Real.log_mul (by norm_num) hδ.ne']; exact Real.log_le_log hr (hle2 θ')
    have : 0 ≤ (2 * π)⁻¹ * (2 * Real.log 2 + 2 * Real.log δ -
        2 * Real.log ‖circleMap v δ θ' - x‖) := mul_nonneg (by positivity) (by linarith)
    simp only [Pi.zero_apply, B]; positivity
  calc ∫⁻ θ' in Ioc 0 (2 * π), ∫⁻ s in Ioc 0 (δ ^ 2),
        ENNReal.ofReal (heatKernel s x (circleMap v δ θ'))
      ≤ ∫⁻ θ' in Ioc 0 (2 * π), ENNReal.ofReal (B θ') := by
        refine lintegral_mono_ae (hae.mono fun θ' hne => ?_)
        have hr : 0 < ‖x - circleMap v δ θ'‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hne))
        have := lintegral_heatKernel_time_le_sq hδ hr (by rw [norm_sub_rev]; exact hle2 θ')
        rwa [norm_sub_rev] at this
    _ = ENNReal.ofReal (∫ θ' in Ioc 0 (2 * π), B θ') :=
        (ofReal_integral_eq_lintegral_ofReal hBi hB0).symm
    _ = _ := by
        congr 1
        rw [← intervalIntegral.integral_of_le (by positivity)]
        have havg := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := x) (c := v)
          hδ.ne'
        rw [Real.circleAverage_def] at havg
        have hvx : ‖v - x‖ = δ := by
          rw [norm_sub_rev]; simp only [x, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hδ]
        rw [hvx, inv_mul_cancel₀ hδ.ne', Real.posLog_one, add_zero] at havg
        have hpos : 0 < 2 * π := by positivity
        have hlog : ∫ θ' in (0 : ℝ)..2 * π, Real.log ‖circleMap v δ θ' - x‖ =
            2 * π * Real.log δ := by
          rw [← havg, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul]
        simp only [B]
        rw [intervalIntegral.integral_add intervalIntegrable_const
            ((intervalIntegrable_const.sub (hI.const_mul 2)).const_mul _),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub intervalIntegrable_const (hI.const_mul 2),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hlog]
        simp only [sub_zero, smul_eq_mul]
        field_simp
        ring

/-- **`G_{v;2}`** (DGo:661–668): `∫∫ (1_{s ≤ δ²} (2π)⁻¹∫ p_{s/2}(v+δe^{iθ}, z) dθ)² ≤
(2π)⁻¹(2 + 2 log 2)`, uniformly in `δ > 0` and `v`. -/
theorem lintegral_freeCircFun_sq_le (hδ : 0 < δ) (v : ℂ) :
    ∫⁻ q, ENNReal.ofReal (freeCircFun (δ ^ 2) δ v q ^ 2) ≤
      ENNReal.ofReal ((2 * π)⁻¹ * (2 + 2 * Real.log 2)) := by
  set T := δ ^ 2
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
  rw [lintegral_congr fun θ => hstep θ]
  calc ENNReal.ofReal ((2 * π)⁻¹) ^ 2 * ∫⁻ θ in I, ∫⁻ θ' in I, ∫⁻ s in Ioc 0 T,
        ENNReal.ofReal (heatKernel s (circleMap v δ θ) (circleMap v δ θ'))
      ≤ ENNReal.ofReal ((2 * π)⁻¹) ^ 2 * ∫⁻ _ in I, ENNReal.ofReal (2 + 2 * Real.log 2) :=
        by gcongr with θ; exact lintegral_circle_time_le_sq hδ v θ
    _ = _ := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, sq, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp

/-- Cauchy–Schwarz for the circle average: `((2π)⁻¹∫ g)² ≤ (2π)⁻¹∫ g²`. -/
lemma sq_avg_le {g : ℝ → ℝ} (hg : Continuous g) :
    ((2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), g θ) ^ 2 ≤ (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), g θ ^ 2 := by
  have hpos : 0 < 2 * π := by positivity
  set m := (2 * π)⁻¹ * ∫ θ in Ioc 0 (2 * π), g θ
  have hi1 : IntegrableOn g (Ioc 0 (2 * π)) :=
    (hg.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn (fun θ => g θ ^ 2) (Ioc 0 (2 * π)) :=
    ((hg.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have h0 : 0 ≤ ∫ θ in Ioc 0 (2 * π), (g θ - m) ^ 2 :=
    setIntegral_nonneg measurableSet_Ioc fun θ _ => sq_nonneg _
  have e : ∫ θ in Ioc 0 (2 * π), (g θ - m) ^ 2 =
      (∫ θ in Ioc 0 (2 * π), g θ ^ 2) - 2 * m * (∫ θ in Ioc 0 (2 * π), g θ) + 2 * π * m ^ 2 := by
    have hfin : volume (Ioc (0 : ℝ) (2 * π)) ≠ ⊤ := measure_Ioc_lt_top.ne
    have this : (fun θ => (g θ - m) ^ 2) = fun θ => (g θ ^ 2 - 2 * m * g θ) + m ^ 2 := by
      funext θ; ring
    have hA : IntegrableOn (fun θ => g θ ^ 2 - 2 * m * g θ) (Ioc 0 (2 * π)) :=
      hi2.sub (hi1.const_mul _)
    rw [this, integral_add (f := fun θ => g θ ^ 2 - 2 * m * g θ) (g := fun _ => m ^ 2)
      hA (integrableOn_const hfin),
      integral_sub (f := fun θ => g θ ^ 2) (g := fun θ => 2 * m * g θ) hi2 (hi1.const_mul _),
      integral_const_mul, setIntegral_const, Real.volume_real_Ioc_of_le hpos.le, sub_zero,
      smul_eq_mul]
  have hm : ∫ θ in Ioc 0 (2 * π), g θ = 2 * π * m := by
    simp only [m]; field_simp
  rw [e, hm] at h0
  have : 2 * π * m ^ 2 ≤ ∫ θ in Ioc 0 (2 * π), g θ ^ 2 := by nlinarith
  rw [le_inv_mul_iff₀ hpos]
  exact this

/-- the `G_{v;4}` kernel in function form: `1_{[δ²,1]}(s)((2π)⁻¹∫ p_{s/2}(v+δe^{iθ}, z) dθ − p_{s/2}(v, z))` -/
def g4Fun (δ : ℝ) (v : ℂ) (q : ℝ × ℂ) : ℝ :=
  (Icc (δ ^ 2) 1 ×ˢ univ).indicator (fun q =>
    (2 * π)⁻¹ * (∫ θ in Ioc 0 (2 * π), circHeat δ v q θ) - heatKernel (q.1 / 2) v q.2) q

lemma measurable_g4Fun : Measurable (g4Fun δ v) := by
  have h := (measurable_circHeat (δ := δ) (v := v)).stronglyMeasurable.integral_prod_right'
    (ν := (volume : Measure ℝ).restrict (Ioc 0 (2 * π)))
  exact ((h.measurable.const_mul _).sub (WhiteNoise.measurable_heatKernel_half v)).indicator
    (measurableSet_Icc.prod MeasurableSet.univ)

lemma measurable_phiKernel_circ (δ : ℝ) (v : ℂ) :
    Measurable fun p : (ℝ × ℂ) × ℝ =>
      (WhiteNoise.phiKernel δ 1 (circleMap v δ p.2) p.1 - WhiteNoise.phiKernel δ 1 v p.1) ^ 2 := by
  have hc : Measurable fun p : (ℝ × ℂ) × ℝ => circleMap v δ p.2 :=
    (continuous_circleMap v δ).measurable.comp measurable_snd
  have h1 : Measurable fun p : (ℝ × ℂ) × ℝ => p.1.1 := measurable_fst.comp measurable_fst
  have h2 : Measurable fun p : (ℝ × ℂ) × ℝ => p.1.2 := measurable_snd.comp measurable_fst
  have hA : Measurable fun p : (ℝ × ℂ) × ℝ => heatKernel (p.1.1 / 2) (circleMap v δ p.2) p.1.2 := by
    unfold heatKernel
    exact ((measurable_const.mul (h1.div_const 2)).inv).mul (Real.measurable_exp.comp
      ((((hc.sub h2).norm.pow_const 2).neg).div (measurable_const.mul (h1.div_const 2))))
  have hS : MeasurableSet {p : (ℝ × ℂ) × ℝ | p.1 ∈ Icc (δ ^ 2) (1 ^ 2) ×ˢ (univ : Set ℂ)} :=
    measurable_fst (measurableSet_Icc.prod MeasurableSet.univ)
  have e : (fun p : (ℝ × ℂ) × ℝ =>
      (WhiteNoise.phiKernel δ 1 (circleMap v δ p.2) p.1 - WhiteNoise.phiKernel δ 1 v p.1) ^ 2) =
      {p : (ℝ × ℂ) × ℝ | p.1 ∈ Icc (δ ^ 2) (1 ^ 2) ×ˢ (univ : Set ℂ)}.indicator
        (fun p => (heatKernel (p.1.1 / 2) (circleMap v δ p.2) p.1.2 -
          heatKernel (p.1.1 / 2) v p.1.2) ^ 2) := by
    funext p
    unfold WhiteNoise.phiKernel
    by_cases hp : p.1 ∈ Icc (δ ^ 2) (1 ^ 2) ×ˢ (univ : Set ℂ)
    · rw [indicator_of_mem (show p ∈ {p : (ℝ × ℂ) × ℝ | p.1 ∈ Icc (δ ^ 2) (1 ^ 2) ×ˢ
        (univ : Set ℂ)} from hp), indicator_of_mem hp, indicator_of_mem hp]
    · rw [indicator_of_notMem (show p ∉ {p : (ℝ × ℂ) × ℝ | p.1 ∈ Icc (δ ^ 2) (1 ^ 2) ×ˢ
        (univ : Set ℂ)} from hp), indicator_of_notMem hp, indicator_of_notMem hp]
      simp
  rw [e]
  exact ((hA.sub ((WhiteNoise.measurable_heatKernel_half v).comp measurable_fst)).pow_const 2).indicator hS

/-- **`G_{v;4}`** (DGo:684–700) in function form: `∫∫ g₄² ≤ 1/π` (`0 < δ`). -/
theorem lintegral_g4Fun_sq_le (hδ : 0 < δ) (v : ℂ) :
    ∫⁻ q, ENNReal.ofReal (g4Fun δ v q ^ 2) ≤ ENNReal.ofReal (1 / π) := by
  have hpos : 0 < 2 * π := by positivity
  obtain hδ1 | hδ1 := lt_or_ge 1 δ
  · have h0 : ∀ q, g4Fun δ v q = 0 := fun q => by
      unfold g4Fun
      refine indicator_of_notMem (fun hq => ?_) _
      have := hq.1.1.trans hq.1.2
      nlinarith
    simp [h0]
  set I := Ioc (0 : ℝ) (2 * π)
  set D : ℝ × ℂ → ℝ → ℝ := fun q θ =>
    WhiteNoise.phiKernel δ 1 (circleMap v δ θ) q - WhiteNoise.phiKernel δ 1 v q
  have hDm := measurable_phiKernel_circ δ v
  -- pointwise Cauchy–Schwarz
  have hpt : ∀ q, ENNReal.ofReal (g4Fun δ v q ^ 2) ≤
      ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ θ in I, ENNReal.ofReal (D q θ ^ 2) := by
    intro q
    by_cases hq : q ∈ Icc (δ ^ 2) 1 ×ˢ (univ : Set ℂ)
    · have hq' : q ∈ Icc (δ ^ 2) (1 ^ 2) ×ˢ (univ : Set ℂ) := by rwa [one_pow]
      have hs : 0 < q.1 := lt_of_lt_of_le (by positivity) hq.1.1
      have hcont : Continuous fun θ => circHeat δ v q θ - heatKernel (q.1 / 2) v q.2 :=
        (continuous_circHeat q).sub continuous_const
      have hDq : ∀ θ, D q θ = circHeat δ v q θ - heatKernel (q.1 / 2) v q.2 := fun θ => by
        simp only [D, WhiteNoise.phiKernel, indicator_of_mem hq', circHeat]
      have hg : g4Fun δ v q = (2 * π)⁻¹ * ∫ θ in I, (circHeat δ v q θ - heatKernel (q.1 / 2) v q.2) := by
        unfold g4Fun
        rw [indicator_of_mem hq, integral_sub ((continuous_circHeat q).integrableOn_Icc.mono_set
          Ioc_subset_Icc_self) (integrableOn_const measure_Ioc_lt_top.ne), setIntegral_const,
          Real.volume_real_Ioc_of_le hpos.le, sub_zero, smul_eq_mul, mul_sub, ← mul_assoc,
          inv_mul_cancel₀ hpos.ne', one_mul]
      have hcs := sq_avg_le hcont
      rw [← hg] at hcs
      have hi : IntegrableOn (fun θ => D q θ ^ 2) I := by
        simp_rw [hDq]; exact ((hcont.pow 2).integrableOn_Icc).mono_set Ioc_subset_Icc_self
      rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun θ =>
        sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal (hcs.trans_eq ?_)
      simp_rw [hDq]; rfl
    · unfold g4Fun; rw [indicator_of_notMem hq]; simp
  have hsw : ∫⁻ q, ∫⁻ θ in I, ENNReal.ofReal (D q θ ^ 2) =
      ∫⁻ θ in I, ∫⁻ q, ENNReal.ofReal (D q θ ^ 2) :=
    lintegral_lintegral_swap (ENNReal.measurable_ofReal.comp hDm).aemeasurable
  have hθ : ∀ θ, ∫⁻ q, ENNReal.ofReal (D q θ ^ 2) ≤ ENNReal.ofReal (1 / π) := by
    intro θ
    have hmem := (WhiteNoise.memLp_phiKernel δ 1 hδ (circleMap v δ θ)).sub
      (WhiteNoise.memLp_phiKernel δ 1 hδ v)
    have hae : (⇑(WhiteNoise.phiKernelL2 δ 1 (circleMap v δ θ) - WhiteNoise.phiKernelL2 δ 1 v) :
        ℝ × ℂ → ℝ) =ᵐ[volume] fun q => D q θ := by
      filter_upwards [Lp.coeFn_sub (WhiteNoise.phiKernelL2 δ 1 (circleMap v δ θ))
        (WhiteNoise.phiKernelL2 δ 1 v), WhiteNoise.coeFn_phiKernelL2 δ 1 hδ (circleMap v δ θ),
        WhiteNoise.coeFn_phiKernelL2 δ 1 hδ v] with q h1 h2 h3
      rw [h1, Pi.sub_apply, h2, h3]
    have hn := DDDF.P29WN.sq_norm_eq_integral hae
    have hb := norm_sqrtPi_smul_phiKernelL2_sub_le hδ hδ1 (circleMap v δ θ) v
    rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hδ, div_self hδ.ne', norm_smul,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hb
    have hsq : Real.pi * ‖WhiteNoise.phiKernelL2 δ 1 (circleMap v δ θ) -
        WhiteNoise.phiKernelL2 δ 1 v‖ ^ 2 ≤ 1 := by
      have h0 := mul_nonneg (Real.sqrt_nonneg Real.pi) (norm_nonneg
        (WhiteNoise.phiKernelL2 δ 1 (circleMap v δ θ) - WhiteNoise.phiKernelL2 δ 1 v))
      have := pow_le_pow_left₀ h0 hb 2
      rwa [mul_pow, Real.sq_sqrt Real.pi_pos.le, one_pow] at this
    have hint : Integrable (fun q => D q θ ^ 2) := hmem.integrable_sq
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun q => sq_nonneg _), ← hn]
    refine ENNReal.ofReal_le_ofReal ?_
    have hπ := Real.pi_pos
    rw [le_div_iff₀ hπ]; linarith
  calc ∫⁻ q, ENNReal.ofReal (g4Fun δ v q ^ 2)
      ≤ ∫⁻ q, ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ θ in I, ENNReal.ofReal (D q θ ^ 2) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ θ in I, ∫⁻ q, ENNReal.ofReal (D q θ ^ 2) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hsw]
    _ ≤ ENNReal.ofReal ((2 * π)⁻¹) * ∫⁻ _ in I, ENNReal.ofReal (1 / π) :=
        by gcongr with θ; exact hθ θ
    _ = ENNReal.ofReal (1 / π) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp

end HeatDir
end DGo
end LQGMetric
