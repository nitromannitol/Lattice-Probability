/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.HeatKernel at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.Blueprint.Draft.LFPPPlan
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Node `HK`: heat-kernel (Frullani) representation of the log kernel

We prove `Blueprint.Draft.LogCovHeatRep`: for zero-mass, nondegenerate segment combinations
`c, c'`,
`c.logCov c' = ∫ t in Ioi 0, gaussPair t c c' / t`.

Structure of the proof.

1. **Frullani at one distance** (`frIntegrand_integrableOn`, `frIntegrand_integral`,
   `frIntegrand_abs_integral`): for `r > 0`,
   `∫_0^∞ (e^{-r²/(4t²)} - e^{-1/(4t²)}) dt/t = -log r`, the integrand is integrable, and its
   absolute integral is `|log r|` (the integrand has constant sign).
2. **Abstract Fubini** (`heatRep_of_integrable_log`): on a finite measure space, if `D > 0`
   a.e. and `log D` is integrable, then
   `∫_0^∞ (∫ e^{-D²/(4t²)} dμ - μ(X) e^{-1/(4t²)}) dt/t = -∫ log D dμ`.
3. **Segments** (`integrable_log_segDist`, `segDist_pos_ae`): for a nondegenerate second
   segment, the distance `D(s,s') = |p(s) - p'(s')|` on `(0,1]²` is a.e. positive and has
   integrable logarithm (projection onto the direction of the second segment).
4. **Per pair** (`pairHeat_rep`): `∫_0^∞ (pairHeat - e^{-1/(4t²)}) dt/t = segLogPair`.
5. **Finite sums** (`logCovHeatRep`): subtracting the reference term does not change the
   double sum since the mass is zero.

Only `c.mass = 0` and `c'.Nondeg` are actually needed (`logCov_eq_integral_gaussPair`).
-/

noncomputable section

open MeasureTheory Filter Topology Set Real

namespace LQGDimension.HeatKernel

open Blueprint.Draft

/-! ## 1. Frullani's integral at a single distance -/

/-- The Frullani integrand at distance `r` with reference distance `1`:
`(e^{-r²/(4t²)} - e^{-1/(4t²)}) / t`. -/
def frIntegrand (r t : ℝ) : ℝ :=
  (Real.exp (-r ^ 2 / (4 * t ^ 2)) - Real.exp (-1 / (4 * t ^ 2))) / t

lemma measurable_frIntegrand (r : ℝ) : Measurable (frIntegrand r) := by
  unfold frIntegrand; fun_prop

/-- `e^{-c/(4t²)} ≤ 4t²/c`. -/
lemma exp_neg_div_four_sq_le {c t : ℝ} (hc : 0 < c) (ht : t ≠ 0) :
    Real.exp (-c / (4 * t ^ 2)) ≤ 4 * t ^ 2 / c := by
  have hx : 0 < c / (4 * t ^ 2) := by positivity
  rw [neg_div, Real.exp_neg]
  calc (Real.exp (c / (4 * t ^ 2)))⁻¹ ≤ (c / (4 * t ^ 2))⁻¹ :=
        inv_anti₀ hx (by linarith [Real.add_one_le_exp (c / (4 * t ^ 2))])
    _ = 4 * t ^ 2 / c := by rw [inv_div]

/-- `exp` is `1`-Lipschitz on `(-∞, 0]`. -/
lemma abs_exp_sub_exp_le_of_nonpos {x y : ℝ} (hx : x ≤ 0) (hy : y ≤ 0) :
    |Real.exp x - Real.exp y| ≤ |x - y| := by
  wlog h : x ≤ y generalizing x y
  · rw [abs_sub_comm, abs_sub_comm x]; exact this hy hx (le_of_not_ge h)
  have h1 : Real.exp x - Real.exp y ≤ 0 := by linarith [Real.exp_le_exp.2 h]
  rw [abs_of_nonpos h1, abs_of_nonpos (by linarith)]
  have h2 : Real.exp x = Real.exp y * Real.exp (x - y) := by rw [← Real.exp_add]; ring_nf
  have h3 : Real.exp y ≤ 1 := Real.exp_le_one_iff.2 hy
  have h4 : Real.exp (x - y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h5 := Real.add_one_le_exp (x - y)
  have h6 := Real.exp_pos y
  rw [h2]
  nlinarith

lemma frIntegrand_integrableOn {r : ℝ} (hr : 0 < r) : IntegrableOn (frIntegrand r) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · refine IntegrableOn.of_bound (by simp [Real.volume_Ioc])
      (measurable_frIntegrand r).aestronglyMeasurable (4 * (1 / r ^ 2 + 1)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hE1 := exp_neg_div_four_sq_le (pow_pos hr 2) ht0.ne'
    have hE2 := exp_neg_div_four_sq_le one_pos ht0.ne'
    have hp1 := Real.exp_pos (-r ^ 2 / (4 * t ^ 2))
    have hp2 := Real.exp_pos (-1 / (4 * t ^ 2))
    have habs : |Real.exp (-r ^ 2 / (4 * t ^ 2)) - Real.exp (-1 / (4 * t ^ 2))| ≤
        4 * t ^ 2 * (1 / r ^ 2 + 1) := by
      have hE2' : Real.exp (-1 / (4 * t ^ 2)) ≤ 4 * t ^ 2 := by simpa using hE2
      have hE1' : Real.exp (-r ^ 2 / (4 * t ^ 2)) ≤ 4 * t ^ 2 * (1 / r ^ 2) := by
        rw [mul_one_div]; exact hE1
      have hq : 0 ≤ 4 * t ^ 2 * (1 / r ^ 2) := by positivity
      have hq' : 0 ≤ 4 * t ^ 2 := by positivity
      rw [abs_le]
      constructor <;> linarith
    rw [Real.norm_eq_abs, frIntegrand, abs_div, abs_of_pos ht0, div_le_iff₀ ht0]
    have hr2 : 0 ≤ 1 / r ^ 2 + 1 := by positivity
    calc _ ≤ 4 * t ^ 2 * (1 / r ^ 2 + 1) := habs
      _ = 4 * (1 / r ^ 2 + 1) * t * t := by ring
      _ ≤ 4 * (1 / r ^ 2 + 1) * t * 1 := by gcongr
      _ = 4 * (1 / r ^ 2 + 1) * t := by ring
  · refine Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1)
      one_pos).const_mul (|r ^ 2 - 1| / 4)) (measurable_frIntegrand r).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans one_pos ht
    have key : |Real.exp (-r ^ 2 / (4 * t ^ 2)) - Real.exp (-1 / (4 * t ^ 2))| ≤
        |r ^ 2 - 1| / (4 * t ^ 2) := by
      refine (abs_exp_sub_exp_le_of_nonpos ?_ ?_).trans (le_of_eq ?_)
      · exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) (by positivity)
      · exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
      · rw [show -r ^ 2 / (4 * t ^ 2) - -1 / (4 * t ^ 2) = -(r ^ 2 - 1) / (4 * t ^ 2) by ring,
          abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 4 * t ^ 2)]
    have hrp : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by
      rw [Real.rpow_neg ht0.le]; norm_num
    rw [Real.norm_eq_abs, frIntegrand, abs_div, abs_of_pos ht0, hrp]
    calc _ ≤ |r ^ 2 - 1| / (4 * t ^ 2) / t := div_le_div_of_nonneg_right key ht0.le
      _ = |r ^ 2 - 1| / 4 * (t ^ 3)⁻¹ := by field_simp

/-- **Frullani's integral** in heat-kernel form: `∫_0^∞ (e^{-r²/(4t²)} - e^{-1/(4t²)}) dt/t
= -log r`. -/
lemma frIntegrand_integral {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi 0, frIntegrand r t = -Real.log r := by
  set f : ℝ → ℝ := fun x => Real.exp (-1 / (4 * x ^ 2)) with hf_def
  have hfun : (fun x : ℝ => x⁻¹ • (f (r⁻¹ * x) - f (1 * x))) = frIntegrand r := by
    funext x
    simp only [hf_def, smul_eq_mul, one_mul, frIntegrand]
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · rw [inv_mul_eq_div]
      have : -1 / (4 * (r⁻¹ * x) ^ 2) = -r ^ 2 / (4 * x ^ 2) := by
        field_simp
      rw [this]
  have hcont : ContinuousOn f (Ioi 0) := by
    refine Real.continuous_exp.comp_continuousOn ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro x hx
    have : (0:ℝ) < x := hx
    positivity
  have hloc : LocallyIntegrableOn f (Ioi 0) := hcont.locallyIntegrableOn measurableSet_Ioi
  have hL : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    have h4 : Tendsto (fun x : ℝ => 4 * x ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Tendsto (fun x : ℝ => 4 * x ^ 2) (𝓝 0) (𝓝 (4 * 0 ^ 2)) :=
          (Continuous.tendsto (by fun_prop) 0)
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        have : (0:ℝ) < x := hx
        show 0 < 4 * x ^ 2
        positivity
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h4.inv_tendsto_nhdsGT_zero
    refine this.congr (fun x => ?_)
    simp [hf_def, Function.comp, neg_div, one_div]
  have hR : Tendsto f atTop (𝓝 1) := by
    have h4 : Tendsto (fun x : ℝ => 4 * x ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).const_mul_atTop four_pos
    have h0 : Tendsto (fun x : ℝ => -1 / (4 * x ^ 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h4
    have := (Real.continuous_exp.tendsto 0).comp h0
    rw [Real.exp_zero] at this
    exact this
  have h := Frullani.integral_Ioi_eq hloc (inv_pos.2 hr) one_pos hL hR
    (by rw [hfun]; exact frIntegrand_integrableOn hr)
  rw [hfun] at h
  rw [h]
  simp

lemma frIntegrand_nonneg {r t : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ht : 0 < t) :
    0 ≤ frIntegrand r t := by
  unfold frIntegrand
  refine div_nonneg ?_ ht.le
  rw [sub_nonneg]
  apply Real.exp_le_exp.2
  have h1 : r ^ 2 ≤ 1 := by nlinarith
  have h4 : 0 < 4 * t ^ 2 := by positivity
  rw [div_le_div_iff_of_pos_right h4]
  linarith

lemma frIntegrand_nonpos {r t : ℝ} (hr1 : 1 ≤ r) (ht : 0 < t) :
    frIntegrand r t ≤ 0 := by
  unfold frIntegrand
  refine div_nonpos_of_nonpos_of_nonneg ?_ ht.le
  rw [sub_nonpos]
  apply Real.exp_le_exp.2
  have h1 : 1 ≤ r ^ 2 := by nlinarith
  have h4 : 0 < 4 * t ^ 2 := by positivity
  rw [div_le_div_iff_of_pos_right h4]
  linarith

/-- The absolute Frullani integral: `∫_0^∞ |e^{-r²/(4t²)} - e^{-1/(4t²)}| dt/t = |log r|`. -/
lemma frIntegrand_abs_integral {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi 0, |frIntegrand r t| = |Real.log r| := by
  rcases le_total r 1 with h | h
  · rw [setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => abs_of_nonneg (frIntegrand_nonneg hr h ht)), frIntegrand_integral hr,
      abs_of_nonpos (Real.log_nonpos hr.le h)]
  · rw [setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => abs_of_nonpos (frIntegrand_nonpos h ht)), integral_neg,
      frIntegrand_integral hr, neg_neg, abs_of_nonneg (Real.log_nonneg h)]

/-! ## 2. Abstract Fubini: heat-kernel representation of `-∫ log D dμ` -/

/-- **Heat-kernel representation of `-∫ log D`.**  On a finite measure space, if `D > 0` a.e.
and `log D` is integrable, then `t ↦ (∫ e^{-D²/(4t²)} dμ - μ(X) e^{-1/(4t²)}) / t` is integrable
on `(0, ∞)` with integral `-∫ log D dμ`. -/
theorem heatRep_of_integrable_log {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (D : X → ℝ) (hD : Measurable D) (hpos : ∀ᵐ x ∂μ, 0 < D x)
    (hlog : Integrable (fun x => Real.log (D x)) μ) :
    IntegrableOn (fun t => (∫ x, Real.exp (-D x ^ 2 / (4 * t ^ 2)) ∂μ -
        μ.real univ * Real.exp (-1 / (4 * t ^ 2))) / t) (Ioi 0) ∧
    ∫ t in Ioi 0, (∫ x, Real.exp (-D x ^ 2 / (4 * t ^ 2)) ∂μ -
        μ.real univ * Real.exp (-1 / (4 * t ^ 2))) / t = -∫ x, Real.log (D x) ∂μ := by
  have hFm : Measurable (fun q : ℝ × X => frIntegrand (D q.2) q.1) := by
    unfold frIntegrand; fun_prop
  have hFi : Integrable (fun q : ℝ × X => frIntegrand (D q.2) q.1)
      ((volume.restrict (Ioi 0)).prod μ) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    constructor
    · filter_upwards [hpos] with x hx
      exact frIntegrand_integrableOn hx
    · refine hlog.abs.congr ?_
      filter_upwards [hpos] with x hx
      simp only [Real.norm_eq_abs]
      rw [frIntegrand_abs_integral hx]
  have hexp : ∀ t : ℝ, Integrable (fun x => Real.exp (-D x ^ 2 / (4 * t ^ 2))) μ := by
    intro t
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)
  have hinner : ∀ t : ℝ, ∫ x, frIntegrand (D x) t ∂μ =
      (∫ x, Real.exp (-D x ^ 2 / (4 * t ^ 2)) ∂μ -
        μ.real univ * Real.exp (-1 / (4 * t ^ 2))) / t := by
    intro t
    simp only [frIntegrand]
    rw [integral_div, integral_sub (hexp t) (integrable_const _), integral_const, smul_eq_mul]
  have hfun : (fun t => (∫ x, Real.exp (-D x ^ 2 / (4 * t ^ 2)) ∂μ -
      μ.real univ * Real.exp (-1 / (4 * t ^ 2))) / t) = fun t => ∫ x, frIntegrand (D x) t ∂μ := by
    funext t; rw [hinner t]
  rw [hfun]
  refine ⟨hFi.integral_prod_left, ?_⟩
  calc ∫ t in Ioi 0, ∫ x, frIntegrand (D x) t ∂μ = ∫ x, (∫ t in Ioi 0, frIntegrand (D x) t) ∂μ :=
        integral_integral_swap (f := fun t x => frIntegrand (D x) t) hFi
    _ = ∫ x, -Real.log (D x) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hpos] with x hx
        exact frIntegrand_integral hx
    _ = -∫ x, Real.log (D x) ∂μ := integral_neg _

/-! ## 3. Segment geometry -/

/-- The unit square `(0,1]²` with Lebesgue measure, as a product measure. -/
def unitSq : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (0 : ℝ) 1))

instance : IsFiniteMeasure unitSq := by unfold unitSq; infer_instance

lemma unitSq_real_univ : unitSq.real univ = 1 := by
  simp [unitSq, measureReal_def, ← Set.univ_prod_univ, Measure.prod_prod, Real.volume_Ioc]

lemma ae_mem_unitSq : ∀ᵐ q ∂unitSq, q ∈ Ioc (0 : ℝ) 1 ×ˢ Ioc (0 : ℝ) 1 := by
  rw [unitSq, Measure.prod_restrict]
  exact ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)

/-- For measurable `σ`, the graph `{q | q.2 = σ q.1}` is null for `unitSq`. -/
lemma ae_ne_graph_unitSq {σ : ℝ → ℝ} (hσ : Measurable σ) : ∀ᵐ q ∂unitSq, q.2 ≠ σ q.1 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  have hms : MeasurableSet {q : ℝ × ℝ | q.2 = σ q.1} :=
    measurableSet_eq_fun measurable_snd (hσ.comp measurable_fst)
  rw [unitSq, Measure.prod_apply hms]
  simp

/-- The distance between the point with parameter `q.1` on `[a,b]` and the point with parameter
`q.2` on `[a',b']`. -/
def segDist (a b a' b' : ℂ) (q : ℝ × ℝ) : ℝ :=
  ‖(a + (q.1 : ℂ) * (b - a)) - (a' + (q.2 : ℂ) * (b' - a'))‖

lemma continuous_segDist (a b a' b' : ℂ) : Continuous (segDist a b a' b') := by
  unfold segDist; fun_prop

/-- Parameter of the orthogonal projection of `a + s(b-a)` onto the line through `a'`, `b'`
(parametrized by `a' + s'(b'-a')`). -/
def segProj (a b a' b' : ℂ) (s : ℝ) : ℝ :=
  ((a + (s : ℂ) * (b - a) - a').re * (b' - a').re +
      (a + (s : ℂ) * (b - a) - a').im * (b' - a').im) /
    ((b' - a').re ^ 2 + (b' - a').im ^ 2)

lemma continuous_segProj (a b a' b' : ℂ) : Continuous (segProj a b a' b') := by
  unfold segProj; fun_prop

/-- Projection lower bound: `‖v‖ |s' - σ| ≤ ‖w - s' v‖`, where `σ` is the projection parameter
of `w` on the line `ℝ v`. -/
lemma proj_lower (w v : ℂ) (hv : v ≠ 0) (s' : ℝ) :
    ‖v‖ * |s' - (w.re * v.re + w.im * v.im) / (v.re ^ 2 + v.im ^ 2)| ≤
      ‖w - (s' : ℂ) * v‖ := by
  have hN : 0 < v.re ^ 2 + v.im ^ 2 := by
    have := Complex.normSq_pos.2 hv
    rw [Complex.normSq_apply] at this; nlinarith
  have hz2 : ‖w - (s' : ℂ) * v‖ ^ 2 = (w.re - s' * v.re) ^ 2 + (w.im - s' * v.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hv2 : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  set e := s' - (w.re * v.re + w.im * v.im) / (v.re ^ 2 + v.im ^ 2) with he
  have hNe : (v.re ^ 2 + v.im ^ 2) * e =
      -(v.re * (w.re - s' * v.re) + v.im * (w.im - s' * v.im)) := by
    rw [he]; field_simp; ring
  have hsq : (‖v‖ * |e|) ^ 2 ≤ ‖w - (s' : ℂ) * v‖ ^ 2 := by
    rw [mul_pow, sq_abs, hv2, hz2]
    have h1 : (v.re ^ 2 + v.im ^ 2) * ((v.re ^ 2 + v.im ^ 2) * e ^ 2) ≤
        (v.re ^ 2 + v.im ^ 2) * ((w.re - s' * v.re) ^ 2 + (w.im - s' * v.im) ^ 2) := by
      have : (v.re ^ 2 + v.im ^ 2) * ((v.re ^ 2 + v.im ^ 2) * e ^ 2) =
          ((v.re ^ 2 + v.im ^ 2) * e) ^ 2 := by ring
      rw [this, hNe, neg_sq]
      nlinarith [sq_nonneg (v.re * (w.im - s' * v.im) - v.im * (w.re - s' * v.re))]
    exact le_of_mul_le_mul_left h1 hN
  have h0 : 0 ≤ ‖v‖ * |e| := by positivity
  calc ‖v‖ * |e| = Real.sqrt ((‖v‖ * |e|) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt (‖w - (s' : ℂ) * v‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖w - (s' : ℂ) * v‖ := Real.sqrt_sq (norm_nonneg _)

/-- The distance between points of two segments is at least `|b'-a'|` times the parameter
distance to the projection. -/
lemma segDist_lower (a b a' b' : ℂ) (hb' : a' ≠ b') (s s' : ℝ) :
    ‖b' - a'‖ * |s' - segProj a b a' b' s| ≤ segDist a b a' b' (s, s') := by
  have h := proj_lower (a + (s : ℂ) * (b - a) - a') (b' - a') (sub_ne_zero.2 (Ne.symm hb')) s'
  have heq : segDist a b a' b' (s, s') =
      ‖(a + (s : ℂ) * (b - a) - a') - (s' : ℂ) * (b' - a')‖ := by
    simp only [segDist]; congr 1; ring
  rw [heq]; exact h

/-- Pointwise bound for `|log D|` off the projection graph. -/
lemma abs_log_segDist_le (a b a' b' : ℂ) (hb' : a' ≠ b') {R : ℝ}
    (hR : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, segDist a b a' b' q ≤ R) (q : ℝ × ℝ)
    (hq : q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) (hne : q.2 ≠ segProj a b a' b' q.1) :
    |Real.log (segDist a b a' b' q)| ≤
      R + |Real.log ‖b' - a'‖| + |Real.log (q.2 - segProj a b a' b' q.1)| := by
  have hlow := segDist_lower a b a' b' hb' q.1 q.2
  have hv : 0 < ‖b' - a'‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hb'))
  have he : 0 < |q.2 - segProj a b a' b' q.1| := abs_pos.2 (sub_ne_zero.2 hne)
  have hm : 0 < ‖b' - a'‖ * |q.2 - segProj a b a' b' q.1| := mul_pos hv he
  have hD : 0 < segDist a b a' b' q := lt_of_lt_of_le hm hlow
  have hDR := hR q hq
  have hn1 := abs_nonneg (Real.log ‖b' - a'‖)
  have hn2 := abs_nonneg (Real.log (q.2 - segProj a b a' b' q.1))
  rcases le_or_gt 1 (segDist a b a' b' q) with h1 | h1
  · rw [abs_of_nonneg (Real.log_nonneg h1)]
    have := Real.log_le_sub_one_of_pos hD
    linarith
  · rw [abs_of_neg (Real.log_neg hD h1)]
    have hlog := Real.log_le_log hm hlow
    rw [Real.log_mul hv.ne' he.ne', Real.log_abs] at hlog
    have := neg_abs_le (Real.log ‖b' - a'‖)
    have := neg_abs_le (Real.log (q.2 - segProj a b a' b' q.1))
    have : 0 ≤ R := le_trans hD.le hDR
    linarith

/-- `s' ↦ |log (s' - c)|` is integrable on `(0,1]`. -/
lemma integrable_abs_log_sub_Ioc (c : ℝ) :
    Integrable (fun s' => |Real.log (s' - c)|) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := 0 - c) (b := 1 - c)).comp_sub_right c
  simp only [sub_add_cancel] at h
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1 h.abs

/-- Uniform bound for `∫_0^1 |log (s' - c)| ds'` over `|c| ≤ K`. -/
lemma setIntegral_abs_log_sub_le {c K : ℝ} (hc : |c| ≤ K) :
    ∫ s' in Ioc (0 : ℝ) 1, |Real.log (s' - c)| ≤ ∫ u in (-(K + 1))..(K + 1), |Real.log u| := by
  rw [← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_comp_sub_right (fun u => |Real.log u|) c]
  have := abs_le.1 hc
  exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
    (ae_of_all _ fun _ => abs_nonneg _) intervalIntegral.intervalIntegrable_log'.abs

/-- For continuous `σ`, `(s, s') ↦ |log (s' - σ s)|` is integrable on `(0,1]²`. -/
lemma integrable_abs_log_sub_unitSq {σ : ℝ → ℝ} (hσ : Continuous σ) :
    Integrable (fun q : ℝ × ℝ => |Real.log (q.2 - σ q.1)|) unitSq := by
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hσ.continuousOn (s := Icc (0 : ℝ) 1))
  have hσm := hσ.measurable
  have hmeas : Measurable (fun q : ℝ × ℝ => |Real.log (q.2 - σ q.1)|) := by fun_prop
  unfold unitSq
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · exact ae_of_all _ fun s => integrable_abs_log_sub_Ioc (σ s)
  · refine Integrable.of_bound hmeas.aestronglyMeasurable.norm.integral_prod_right'
      (∫ u in (-(K + 1))..(K + 1), |Real.log u|) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have hKs : |σ s| ≤ K := by simpa [Real.norm_eq_abs] using hK s (Ioc_subset_Icc_self hs)
    simp only [Real.norm_eq_abs, abs_abs]
    rw [abs_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
    exact setIntegral_abs_log_sub_le hKs

/-- If the second segment is nondegenerate, `log D` is integrable on `(0,1]²`. -/
lemma integrable_log_segDist (a b a' b' : ℂ) (hb' : a' ≠ b') :
    Integrable (fun q => Real.log (segDist a b a' b' q)) unitSq := by
  obtain ⟨R, hR⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (continuous_segDist a b a' b').continuousOn
  have hR' : ∀ q ∈ Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1, segDist a b a' b' q ≤ R := fun q hq =>
    (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hR q hq)
  have hg : Integrable (fun q : ℝ × ℝ => R + |Real.log ‖b' - a'‖| +
      |Real.log (q.2 - segProj a b a' b' q.1)|) unitSq :=
    (integrable_const _).add (integrable_abs_log_sub_unitSq (continuous_segProj a b a' b'))
  refine hg.mono' (continuous_segDist a b a' b').measurable.log.aestronglyMeasurable ?_
  filter_upwards [ae_mem_unitSq, ae_ne_graph_unitSq (continuous_segProj a b a' b').measurable]
    with q hq hne
  rw [Real.norm_eq_abs]
  exact abs_log_segDist_le a b a' b' hb' hR' q
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self hq) hne

/-- If the second segment is nondegenerate, `D > 0` a.e. on `(0,1]²`. -/
lemma segDist_pos_ae (a b a' b' : ℂ) (hb' : a' ≠ b') :
    ∀ᵐ q ∂unitSq, 0 < segDist a b a' b' q := by
  filter_upwards [ae_ne_graph_unitSq (continuous_segProj a b a' b').measurable] with q hne
  have hv : 0 < ‖b' - a'‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hb'))
  have he : 0 < |q.2 - segProj a b a' b' q.1| := abs_pos.2 (sub_ne_zero.2 hne)
  exact lt_of_lt_of_le (mul_pos hv he) (segDist_lower a b a' b' hb' q.1 q.2)

/-! ## 4. One pair of segments -/

/-- The Gaussian-kernel pairing of two uniform segment measures (one entry of `gaussPair`). -/
def pairHeat (a b a' b' : ℂ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ s' in (0 : ℝ)..1,
    Real.exp (-‖(a + (s : ℂ) * (b - a)) - (a' + (s' : ℂ) * (b' - a'))‖ ^ 2 / (4 * t ^ 2))

lemma integrable_exp_heat {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {D : X → ℝ} (hD : Measurable D) (t : ℝ) :
    Integrable (fun x => Real.exp (-D x ^ 2 / (4 * t ^ 2))) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

lemma pairHeat_eq (a b a' b' : ℂ) (t : ℝ) :
    pairHeat a b a' b' t = ∫ q, Real.exp (-segDist a b a' b' q ^ 2 / (4 * t ^ 2)) ∂unitSq := by
  have hint := integrable_exp_heat unitSq (continuous_segDist a b a' b').measurable t
  unfold unitSq at hint ⊢
  rw [integral_prod _ hint]
  simp only [pairHeat, intervalIntegral.integral_of_le zero_le_one, segDist]

lemma segLogPair_eq (a b a' b' : ℂ) (hb' : a' ≠ b') :
    segLogPair a b a' b' = -∫ q, Real.log (segDist a b a' b' q) ∂unitSq := by
  have hint : Integrable (fun q => -Real.log (segDist a b a' b' q)) unitSq :=
    (integrable_log_segDist a b a' b' hb').neg
  rw [← integral_neg]
  unfold unitSq at hint ⊢
  rw [integral_prod _ hint]
  simp only [segLogPair, intervalIntegral.integral_of_le zero_le_one, segDist]

/-- **Heat-kernel representation for one pair of segments.**  If `[a', b']` is nondegenerate,
`∫_0^∞ (pairHeat a b a' b' t - e^{-1/(4t²)}) dt/t = segLogPair a b a' b'`, with an integrable
integrand. -/
theorem pairHeat_rep (a b a' b' : ℂ) (hb' : a' ≠ b') :
    IntegrableOn (fun t => (pairHeat a b a' b' t - Real.exp (-1 / (4 * t ^ 2))) / t) (Ioi 0) ∧
    ∫ t in Ioi 0, (pairHeat a b a' b' t - Real.exp (-1 / (4 * t ^ 2))) / t =
      segLogPair a b a' b' := by
  obtain ⟨h1, h2⟩ := heatRep_of_integrable_log unitSq (segDist a b a' b')
    (continuous_segDist a b a' b').measurable (segDist_pos_ae a b a' b' hb')
    (integrable_log_segDist a b a' b' hb')
  simp only [unitSq_real_univ, one_mul] at h1 h2
  have hfun : (fun t => (pairHeat a b a' b' t - Real.exp (-1 / (4 * t ^ 2))) / t) =
      fun t => (∫ q, Real.exp (-segDist a b a' b' q ^ 2 / (4 * t ^ 2)) ∂unitSq -
        Real.exp (-1 / (4 * t ^ 2))) / t := by
    funext t; rw [pairHeat_eq]
  rw [hfun, segLogPair_eq a b a' b' hb']
  exact ⟨h1, h2⟩

/-! ## 5. Finite sums -/

/-- Integral of a finite list sum of integrable functions. -/
lemma integral_list_sum_map {α Y : Type*} [MeasurableSpace Y] {μ : Measure Y}
    (l : List α) (f : α → Y → ℝ) (hf : ∀ a ∈ l, Integrable (f a) μ) :
    Integrable (fun y => (l.map fun a => f a y).sum) μ ∧
      ∫ y, (l.map fun a => f a y).sum ∂μ = (l.map fun a => ∫ y, f a y ∂μ).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hf a (by simp)
    obtain ⟨h1, h2⟩ := ih (fun b hb => hf b (List.mem_cons_of_mem _ hb))
    simp only [List.map_cons, List.sum_cons]
    exact ⟨ha.add h1, by rw [integral_add ha h1, h2]⟩

lemma inner_ref_sum (w : ℝ) (c' : SegComb) (g : ℝ × ℂ × ℂ → ℝ) (K t : ℝ) :
    (c'.map fun p' => w * p'.1 * ((g p' - K) / t)).sum =
      (c'.map fun p' => w * p'.1 * g p').sum / t - w * (c'.map fun p' => p'.1).sum * K / t := by
  induction c' with
  | nil => simp
  | cons p' c' ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Subtracting a reference kernel `K` from every entry changes the weighted double sum by
`mass c * mass c' * K`. -/
lemma outer_ref_sum (c c' : SegComb) (G : ℝ × ℂ × ℂ → ℝ × ℂ × ℂ → ℝ) (K t : ℝ) :
    (c.map fun p => (c'.map fun p' => p.1 * p'.1 * ((G p p' - K) / t)).sum).sum =
      (c.map fun p => (c'.map fun p' => p.1 * p'.1 * G p p').sum).sum / t -
        (c.map fun p => p.1).sum * (c'.map fun p' => p'.1).sum * K / t := by
  induction c with
  | nil => simp
  | cons p c ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, inner_ref_sum p.1 c' (G p) K t]
    ring

/-- `gaussPair` in terms of `pairHeat`. -/
lemma gaussPair_eq (t : ℝ) (c c' : SegComb) :
    gaussPair t c c' = (c.map fun p => (c'.map fun p' =>
      p.1 * p'.1 * pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t).sum).sum := rfl

/-- **Heat-kernel representation of `logCov`**, under the minimal hypotheses: `c` has zero mass
and every weighted segment of `c'` is nondegenerate.  Also records that `t ↦ gaussPair t c c' / t`
is integrable on `(0, ∞)`. -/
theorem gaussPair_heatRep (c c' : SegComb) (hc : c.mass = 0) (hnc' : c'.Nondeg) :
    IntegrableOn (fun t => gaussPair t c c' / t) (Ioi 0) ∧
      c.logCov c' = ∫ t in Ioi (0 : ℝ), gaussPair t c c' / t := by
  have hrw : (fun t => gaussPair t c c' / t) = fun t => (c.map fun p => (c'.map fun p' =>
      p.1 * p'.1 * ((pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t - Real.exp (-1 / (4 * t ^ 2))) / t)).sum).sum := by
    funext t
    have h := outer_ref_sum c c' (fun p p' => pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t)
      (Real.exp (-1 / (4 * t ^ 2))) t
    have hm : (c.map fun p => p.1).sum = 0 := hc
    simp only [hm, zero_mul, zero_div, sub_zero] at h
    rw [gaussPair_eq]
    exact h.symm
  have hpair : ∀ p ∈ c, ∀ p' ∈ c',
      IntegrableOn (fun t => p.1 * p'.1 *
        ((pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t - Real.exp (-1 / (4 * t ^ 2))) / t)) (Ioi 0) ∧
      ∫ t in Ioi 0, p.1 * p'.1 *
        ((pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t - Real.exp (-1 / (4 * t ^ 2))) / t) =
        p.1 * p'.1 * segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2 := by
    intro p _ p' hp'
    by_cases hw : p'.1 = 0
    · simp [hw]
    · obtain ⟨h1, h2⟩ := pairHeat_rep p.2.1 p.2.2 p'.2.1 p'.2.2 (hnc' p' hp' hw)
      exact ⟨h1.const_mul _, by rw [integral_const_mul, h2]⟩
  have hin : ∀ p ∈ c,
      IntegrableOn (fun t => (c'.map fun p' => p.1 * p'.1 *
        ((pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t - Real.exp (-1 / (4 * t ^ 2))) / t)).sum)
        (Ioi 0) ∧
      ∫ t in Ioi 0, (c'.map fun p' => p.1 * p'.1 *
        ((pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t - Real.exp (-1 / (4 * t ^ 2))) / t)).sum =
        (c'.map fun p' => p.1 * p'.1 * segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2).sum := by
    intro p hp
    obtain ⟨h1, h2⟩ := integral_list_sum_map (μ := volume.restrict (Ioi 0)) c'
      (fun (p' : ℝ × ℂ × ℂ) (t : ℝ) => p.1 * p'.1 *
        ((pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t - Real.exp (-1 / (4 * t ^ 2))) / t))
      (fun p' hp' => (hpair p hp p' hp').1)
    exact ⟨h1, h2.trans (congrArg List.sum
      (List.map_congr_left fun p' hp' => (hpair p hp p' hp').2))⟩
  obtain ⟨h1, h2⟩ := integral_list_sum_map (μ := volume.restrict (Ioi 0)) c
    (fun (p : ℝ × ℂ × ℂ) (t : ℝ) => (c'.map fun (p' : ℝ × ℂ × ℂ) => p.1 * p'.1 *
      ((pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t - Real.exp (-1 / (4 * t ^ 2))) / t)).sum)
    (fun p hp => (hin p hp).1)
  refine ⟨by rw [hrw]; exact h1, ?_⟩
  calc c.logCov c' = (c.map fun p => (c'.map fun p' =>
        p.1 * p'.1 * segLogPair p.2.1 p.2.2 p'.2.1 p'.2.2).sum).sum := rfl
    _ = (c.map fun p => ∫ t in Ioi 0, (c'.map fun p' => p.1 * p'.1 *
        ((pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t - Real.exp (-1 / (4 * t ^ 2))) / t)).sum).sum :=
        congrArg List.sum (List.map_congr_left fun p hp => (hin p hp).2.symm)
    _ = ∫ t in Ioi 0, (c.map fun p => (c'.map fun p' => p.1 * p'.1 *
        ((pairHeat p.2.1 p.2.2 p'.2.1 p'.2.2 t - Real.exp (-1 / (4 * t ^ 2))) / t)).sum).sum :=
        h2.symm
    _ = ∫ t in Ioi (0 : ℝ), gaussPair t c c' / t := by rw [hrw]

theorem integrableOn_gaussPair_div (c c' : SegComb) (hc : c.mass = 0) (hnc' : c'.Nondeg) :
    IntegrableOn (fun t => gaussPair t c c' / t) (Ioi 0) :=
  (gaussPair_heatRep c c' hc hnc').1

theorem logCov_eq_integral_gaussPair (c c' : SegComb) (hc : c.mass = 0) (hnc' : c'.Nondeg) :
    c.logCov c' = ∫ t in Ioi (0 : ℝ), gaussPair t c c' / t :=
  (gaussPair_heatRep c c' hc hnc').2

end LQGDimension.HeatKernel

namespace LQGDimension

/-- **Node `HK`** (`Blueprint.Draft.LogCovHeatRep`): on zero-mass nondegenerate segment
combinations, `c.logCov c' = ∫_0^∞ gaussPair t c c' dt/t`. -/
theorem logCovHeatRep : Blueprint.Draft.LogCovHeatRep :=
  fun c c' hc _ _ hnc' => HeatKernel.logCov_eq_integral_gaussPair c c' hc hnc'

end LQGDimension
