import LatticeProb.Bonanno.SupercriticalLFPPAS.Field.LocalizedHeatEstimates
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_2
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge
import LatticeProb.Analysis.GaussianRadialAverage
import LatticeProb.Probability.WeightedAverageSecondMoment
import LatticeProb.Probability.HeatCircleAverageGaussian
import LatticeProb.Gauss.IsonormalSum

/-!
# Second moment of the heat-kernel mollification minus the circle average

Let `h` be a whole-plane Gaussian free field normalized by `h_1(0) = 0`, with circle averages
`h_r(z)` and heat-kernel mollification `h*_ε(z)`. For every continuous version of the circle
average process, the heat-kernel mollification is the average of the circle averages against
the radial Gaussian weight:
`h*_ε(z) - h_ε(z) = ∫_0^∞ 2u e^{-u²} (h_{εu}(z) - h_ε(z)) du`.
The same-centre increment `h_{εu}(z) - h_ε(z)` is a centered Gaussian of variance `|log u|`, so
Jensen's inequality for the probability measure `2u e^{-u²} du` gives the scale-free bound
`E[(h*_ε(z) - h_ε(z))²] ≤ ∫_0^∞ 2u e^{-u²} |log u| du`,
uniformly in the scale `ε > 0` and the centre `z`.

## Main results

* `gaussRadialMeasure`: the probability measure `2u e^{-u²} du` on `(0, ∞)`;
* `lintegral_sq_cInc_sameCentre`: `E[(h_r(z) - h_s(z))²] = |log r - log s|`;
* `lintegral_sq_heatMollify_sub_circleAvg_le`: the second-moment bound above;
* `heatCircleVarConst`, `integrableOn_gaussRadial_abs_log`: the constant is finite;
* `exists_gaussianReal_heatMollify_sub_circleAvg_le`: the centered Gaussian law `N(0, V)` of
  `h*_ε(z) - h_ε(z)` has `V ≤ ∫_0^∞ 2u e^{-u²} |log u| du`, uniformly in `ε` and `z`;
* `measure_abs_heatMollify_sub_circleAvg_ge_le`: the Gaussian tail bound
  `P(|h*_ε(z) - h_ε(z)| ≥ T) ≤ 2 exp(-T² / (2 V₀))`, uniformly in `ε` and `z`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

noncomputable section

namespace LQGMetric.HeatCircle

/-! ## The radial Gaussian weight as a probability measure -/

/-- The radial Gaussian weight `2u e^{-u²} du` on `(0, ∞)`, as a measure on the subtype. -/
def gaussRadialMeasure : Measure (Ioi (0 : ℝ)) :=
  ((volume : Measure ℝ).comap Subtype.val).withDensity
    fun u => ENNReal.ofReal (2 * (u : ℝ) * Real.exp (-(u : ℝ) ^ 2))

lemma measurable_gaussRadialDensity :
    Measurable fun u : Ioi (0 : ℝ) => ENNReal.ofReal (2 * (u : ℝ) * Real.exp (-(u : ℝ) ^ 2)) :=
  ENNReal.measurable_ofReal.comp (by fun_prop)

lemma lintegral_gaussRadialMeasure {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ u, g u ∂gaussRadialMeasure =
      ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (2 * u * Real.exp (-u ^ 2)) * g u := by
  unfold gaussRadialMeasure
  exact (lintegral_withDensity_eq_lintegral_mul _ measurable_gaussRadialDensity
    (hg.comp measurable_subtype_coe)).trans (lintegral_subtype_comap measurableSet_Ioi
    (fun u : ℝ => ENNReal.ofReal (2 * u * Real.exp (-u ^ 2)) * g u))

lemma integral_gaussRadialMeasure (f : ℝ → ℝ) :
    ∫ u, f u ∂gaussRadialMeasure = ∫ u in Ioi (0 : ℝ), 2 * u * Real.exp (-u ^ 2) * f u := by
  rw [gaussRadialMeasure, integral_withDensity_eq_integral_toReal_smul
    measurable_gaussRadialDensity (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    ← integral_subtype_comap measurableSet_Ioi
      (fun u : ℝ => 2 * u * Real.exp (-u ^ 2) * f u)]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  have hu : 0 < (u : ℝ) := mem_Ioi.mp u.2
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (mul_pos (mul_pos two_pos hu) (Real.exp_pos _)).le]

instance : IsProbabilityMeasure gaussRadialMeasure := by
  constructor
  have h := lintegral_gaussRadialMeasure (g := fun _ => 1) measurable_const
  rw [lintegral_one] at h
  rw [h]
  simp only [mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal
      LatticeProb.GaussianRadialAverage.integrableOn_two_mul_exp_neg_sq ?_,
    LatticeProb.GaussianRadialAverage.integral_two_mul_exp_neg_sq, ENNReal.ofReal_one]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  exact (mul_pos (mul_pos two_pos (mem_Ioi.mp hu)) (Real.exp_pos _)).le

/-! ## Same-centre increments of the circle average -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- The second moment of a random variable with law `N(0, v)` is `v`. -/
lemma lintegral_sq_eq_of_map_eq_gaussianReal {X : Ω → ℝ} (hX : Measurable X) {v : NNReal}
    (hmap : P.map X = gaussianReal 0 v) :
    ∫⁻ ω, ENNReal.ofReal (X ω ^ 2) ∂P = ENNReal.ofReal v := by
  rw [← lintegral_map (f := fun x : ℝ => ENNReal.ofReal (x ^ 2)) (by fun_prop) hX, hmap]
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 v) :=
    (memLp_id_gaussianReal 2).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun x => sq_nonneg x)]
  have hvar := variance_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral measurable_id.aemeasurable] at hvar
  simp only [id_eq] at hvar
  rw [integral_id_gaussianReal] at hvar
  simp only [sub_zero] at hvar
  rw [hvar]

/-- The increment covariance of two concentric circles: `|log r - log s|`. -/
lemma incCov_sameCentre (z : ℂ) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    CircleAvg.incCov z r z s z r z s = |Real.log r - Real.log s| := by
  rw [CircleAvg.incCov, CircleAvg.circCov_center z hr r hr, CircleAvg.circCov_center z hr s hs,
    CircleAvg.circCov_center z hs r hr, CircleAvg.circCov_center z hs s hs,
    inv_mul_cancel₀ hr.ne', inv_mul_cancel₀ hs.ne']
  have h1 : Real.posLog 1 = 0 := by simp [Real.posLog_apply]
  have hinv : (s⁻¹ * r)⁻¹ = r⁻¹ * s := by rw [mul_inv, inv_inv, mul_comm]
  have hlog : Real.log (s⁻¹ * r) = Real.log r - Real.log s := by
    rw [Real.log_mul (inv_ne_zero hs.ne') hr.ne', Real.log_inv]; ring
  rw [← hlog, Real.abs_log_eq_posLog_add_posLog_inv, hinv, h1]
  ring

/-- **Second moment of a same-centre increment** of the circle average of a whole-plane GFF:
`E[(h_r(z) - h_s(z))²] = |log r - log s|`. -/
theorem lintegral_sq_cInc_sameCentre (hh : IsWholePlaneGFF h P) {r s : ℝ} (hr : 0 < r)
    (hs : 0 < s) (z : ℂ) :
    ∫⁻ ω, ENNReal.ofReal (CircleAvg.cInc h r z s z ω ^ 2) ∂P =
      ENNReal.ofReal |Real.log r - Real.log s| := by
  have hm := CircleAvg.measurable_cInc hh r z s z
  obtain ⟨hmap, -⟩ := CircleAvg.map_cInc hh hr hs z z
  rw [incCov_sameCentre z hr hs] at hmap
  set v : NNReal := (|Real.log r - Real.log s|).toNNReal
  have hv : (v : ℝ) = |Real.log r - Real.log s| := Real.coe_toNNReal _ (abs_nonneg _)
  rw [lintegral_sq_eq_of_map_eq_gaussianReal hm hmap, hv]

/-! ## The second-moment bound -/

/-- **Heat-kernel mollification versus circle average, second moment.** For a whole-plane GFF
normalized by `h_1(0) = 0`, every scale `ε > 0` and every centre `z`,
`E[(h*_ε(z) - h_ε(z))²] ≤ ∫_0^∞ 2u e^{-u²} |log u| du`. -/
theorem lintegral_sq_heatMollify_sub_circleAvg_le
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) :
    ∫⁻ ω, ENNReal.ofReal ((heatMollify ε (h ω) z - circleAvg (h ω) ε z) ^ 2) ∂P ≤
      ∫⁻ u in Ioi (0 : ℝ),
        ENNReal.ofReal (2 * u * Real.exp (-u ^ 2)) * ENNReal.ofReal |Real.log u| := by
  have hW := hh.1
  classical
  have := hW.gaussian.isProbabilityMeasure
  obtain ⟨H, hH⟩ := DFGPS.exists_isCircleAvgVersion hW
  -- the same-centre increment process, indexed by `u > 0`
  set X : Ioi (0 : ℝ) → Ω → ℝ := fun u ω => H (ε * u) z ω - H ε z ω with hXdef
  have hXcont : ∀ ω, Continuous fun u : Ioi (0 : ℝ) => X u ω := by
    intro ω
    have hc := (hH.cont ω).comp_continuous
      (f := fun u : Ioi (0 : ℝ) => ((ε * (u : ℝ) : ℝ), z)) (by fun_prop)
      (fun u => ⟨mul_pos hε (mem_Ioi.mp u.2), mem_univ _⟩)
    exact hc.sub continuous_const
  have hXae : ∀ u : Ioi (0 : ℝ), X u =ᵐ[P] CircleAvg.cInc h (ε * u) z ε z := by
    intro u
    filter_upwards [hH.ae_eq (ε * u) (mul_pos hε (mem_Ioi.mp u.2)) z, hH.ae_eq ε hε z]
      with ω h1 h2
    simp only [hXdef, CircleAvg.cInc, h1, h2]
  -- a measurable null set off which `X` agrees with the increments at all rational radii
  have hG : ∀ᵐ ω ∂P, ∀ q : ℚ, ∀ hq : 0 < (q : ℝ),
      X ⟨q, hq⟩ ω = CircleAvg.cInc h (ε * q) z ε z ω := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [hXae ⟨q, hq⟩] with ω hω
      exact fun _ => hω
    · exact ae_of_all _ fun _ hq' => absurd hq' hq
  set N : Set Ω := toMeasurable P {ω | ¬ ∀ q : ℚ, ∀ hq : 0 < (q : ℝ),
      X ⟨q, hq⟩ ω = CircleAvg.cInc h (ε * q) z ε z ω} with hNdef
  have hN0 : P N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hG
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hNc : ∀ ω ∉ N, ∀ q : ℚ, ∀ hq : 0 < (q : ℝ),
      X ⟨q, hq⟩ ω = CircleAvg.cInc h (ε * q) z ε z ω := by
    intro ω hω
    by_contra hc
    exact hω (subset_toMeasurable _ _ hc)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    refine ae_iff.2 ?_
    simp only [not_not, ofPred_mem_eq]
    exact hN0
  -- the measurable modification
  set X' : Ioi (0 : ℝ) → Ω → ℝ := fun u ω => if ω ∈ N then 0 else X u ω with hX'def
  have hX'cont : ∀ ω, Continuous fun u : Ioi (0 : ℝ) => X' u ω := by
    intro ω
    by_cases hω : ω ∈ N
    · simp only [hX'def, hω, ite_true]; exact continuous_const
    · simp only [hX'def, hω, ite_false]; exact hXcont ω
  have hX'meas : ∀ u : Ioi (0 : ℝ), Measurable (X' u) := by
    intro u
    have hu : 0 < (u : ℝ) := mem_Ioi.mp u.2
    have hex : ∀ n : ℕ, ∃ q : ℚ, (u : ℝ) < q ∧ (q : ℝ) < u + 1 / ((n : ℝ) + 1) := fun n =>
      exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                          linarith)
    choose q hq1 hq2 using hex
    have hqpos : ∀ n, 0 < (q n : ℝ) := fun n => hu.trans (hq1 n)
    have hqt : Tendsto (fun n => (q n : ℝ)) atTop (𝓝 u) := by
      have hlim : Tendsto (fun n : ℕ => (u : ℝ) + 1 / ((n : ℝ) + 1)) atTop (𝓝 u) := by
        have h0 := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add (u : ℝ)
        rwa [add_zero] at h0
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun n => (hq1 n).le) (fun n => (hq2 n).le)
    have hsub : Tendsto (fun n => (⟨q n, hqpos n⟩ : Ioi (0 : ℝ))) atTop (𝓝 u) :=
      tendsto_subtype_rng.2 hqt
    refine measurable_of_tendsto_metrizable
      (f := fun n ω => if ω ∈ N then 0 else CircleAvg.cInc h (ε * q n) z ε z ω)
      (fun n => Measurable.ite hNm measurable_const (CircleAvg.measurable_cInc hW _ _ _ _)) ?_
    rw [tendsto_pi_nhds]
    intro ω
    by_cases hω : ω ∈ N
    · simp only [hX'def, hω, ite_true]; exact tendsto_const_nhds
    · simp only [hX'def, hω, ite_false]
      have heq : ∀ n, CircleAvg.cInc h (ε * q n) z ε z ω = X ⟨q n, hqpos n⟩ ω :=
        fun n => (hNc ω hω (q n) (hqpos n)).symm
      simp only [heq]
      exact ((hXcont ω).tendsto u).comp hsub
  have hX'm : Measurable (Function.uncurry X') :=
    measurable_uncurry_of_continuous_of_measurable hX'cont hX'meas
  -- Jensen's inequality for the radial Gaussian weight
  have hJ := LatticeProb.WeightedAverageSecondMoment.lintegral_sq_integral_le
    (μ := gaussRadialMeasure) (P := P) X' hX'm
  -- the right side: second moments of the increments
  have hRHS : ∀ u : Ioi (0 : ℝ),
      ∫⁻ ω, ENNReal.ofReal (X' u ω ^ 2) ∂P = ENNReal.ofReal |Real.log u| := by
    intro u
    have hu : 0 < (u : ℝ) := mem_Ioi.mp u.2
    have hae : (fun ω => ENNReal.ofReal (X' u ω ^ 2)) =ᵐ[P]
        fun ω => ENNReal.ofReal (CircleAvg.cInc h (ε * u) z ε z ω ^ 2) := by
      filter_upwards [hNae, hXae u] with ω hω hXω
      simp only [hX'def, hω, ite_false, hXω]
    rw [lintegral_congr_ae hae, lintegral_sq_cInc_sameCentre hW (mul_pos hε hu) hε z,
      Real.log_mul hε.ne' hu.ne']
    congr 2
    ring
  -- the left side: the radial identity
  have hLHS : (fun ω => ENNReal.ofReal ((heatMollify ε (h ω) z - circleAvg (h ω) ε z) ^ 2))
      =ᵐ[P] fun ω => ENNReal.ofReal ((∫ u, X' u ω ∂gaussRadialMeasure) ^ 2) := by
    obtain ⟨A, hA, hAb⟩ := DFGPS.lem2_2 hW hH (‖z‖ + 1)
    filter_upwards [SupercriticalLFPPAS.Field.ae_heatMollify_eq_polarInt_forVersion P h hh H hH,
      hH.ae_eq ε hε z, hAb (1 / 2) (by norm_num), hNae] with ω hHω hCω hGω hNω
    obtain ⟨C₀, hC₀⟩ := hGω
    have hzb : z ∈ Metric.ball (0 : ℂ) (‖z‖ + 1) := mem_ball_zero_iff.2 (by linarith)
    have hF : ∀ r, 0 < r → |H r z ω| ≤ |C₀| * (A / r + r + 1) := fun r hr =>
      SupercriticalLQGUniqueness.B2.Polylog.abs_le_of_lem2_2 hA.le hr (hC₀ r hr z hzb)
    have hFc : ContinuousOn (fun r => H r z ω) (Ioi 0) :=
      (hH.cont ω).comp (continuousOn_id.prodMk continuousOn_const)
        (fun r hr => ⟨hr, mem_univ _⟩)
    have hInt := SupercriticalLFPPAS.Field.integrableOn_polarIntegrand_gauss hε hA.le
      (abs_nonneg C₀) hF hFc (w := fun _ => 1) (fun _ => by simp) continuousOn_const
    simp only [mul_one] at hInt
    have hid := LatticeProb.GaussianRadialAverage.gaussRadial_integral_sub_self_eq
      (fun r => H r z ω) hε hInt
    have hX'ω : ∫ u, X' u ω ∂gaussRadialMeasure =
        ∫ u in Ioi (0 : ℝ), 2 * u * Real.exp (-u ^ 2) * (H (ε * u) z ω - H ε z ω) := by
      rw [← integral_gaussRadialMeasure]
      refine integral_congr_ae (ae_of_all _ fun u => ?_)
      simp only [hX'def, hNω, ite_false, hXdef]
    rw [hX'ω, ← hid, hHω ε hε z, ← hCω]
    simp only [SupercriticalLQGUniqueness.B2.Polylog.polarInt, mul_one]
  rw [lintegral_congr_ae hLHS]
  refine hJ.trans (le_of_eq ?_)
  rw [lintegral_congr hRHS]
  exact lintegral_gaussRadialMeasure (g := fun u => ENNReal.ofReal |Real.log u|)
    (by fun_prop)

/-! ## The scale-free constant and the variance bound -/

/-- The radial Gaussian average of `|log u|`: `V₀ = ∫_0^∞ 2u e^{-u²} |log u| du`. -/
def heatCircleVarConst : ℝ := ∫ u in Ioi (0 : ℝ), 2 * u * Real.exp (-u ^ 2) * |Real.log u|

lemma abs_log_le_inv_add_self {u : ℝ} (hu : 0 < u) : |Real.log u| ≤ u⁻¹ + u := by
  have h1 := Real.log_le_sub_one_of_pos hu
  have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hu)
  rw [Real.log_inv] at h2
  have h3 : 0 < u⁻¹ := inv_pos.mpr hu
  rw [abs_le]
  constructor <;> linarith

lemma integrableOn_gaussRadial_abs_log :
    IntegrableOn (fun u : ℝ => 2 * u * Real.exp (-u ^ 2) * |Real.log u|) (Ioi 0) := by
  have hg : Integrable (fun u : ℝ =>
      2 * Real.exp (-1 * u ^ 2) + 2 * (u ^ (2 : ℝ) * Real.exp (-1 * u ^ 2))) :=
    ((integrable_exp_neg_mul_sq one_pos).const_mul 2).add
      ((integrable_rpow_mul_exp_neg_mul_sq one_pos (by norm_num : (-1 : ℝ) < 2)).const_mul 2)
  have hmeas : Measurable fun u : ℝ => 2 * u * Real.exp (-u ^ 2) * |Real.log u| := by
    fun_prop
  refine hg.integrableOn.mono' hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hu : 0 < u := mem_Ioi.mp hu
  have hw : 0 ≤ 2 * u * Real.exp (-u ^ 2) := (mul_pos (mul_pos two_pos hu) (Real.exp_pos _)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw (abs_nonneg _)), Real.rpow_two, neg_one_mul]
  calc 2 * u * Real.exp (-u ^ 2) * |Real.log u| ≤ 2 * u * Real.exp (-u ^ 2) * (u⁻¹ + u) :=
        mul_le_mul_of_nonneg_left (abs_log_le_inv_add_self hu) hw
    _ = 2 * Real.exp (-u ^ 2) + 2 * (u ^ 2 * Real.exp (-u ^ 2)) := by
        have : u * u⁻¹ = 1 := mul_inv_cancel₀ hu.ne'
        linear_combination (2 * Real.exp (-u ^ 2)) * this

lemma heatCircleVarConst_nonneg : 0 ≤ heatCircleVarConst :=
  setIntegral_nonneg measurableSet_Ioi fun _ hu =>
    mul_nonneg (mul_pos (mul_pos two_pos (mem_Ioi.mp hu)) (Real.exp_pos _)).le (abs_nonneg _)

lemma lintegral_gaussRadial_abs_log_eq :
    ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (2 * u * Real.exp (-u ^ 2)) * ENNReal.ofReal |Real.log u| =
      ENNReal.ofReal heatCircleVarConst := by
  rw [heatCircleVarConst, ofReal_integral_eq_lintegral_ofReal integrableOn_gaussRadial_abs_log]
  · refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [ENNReal.ofReal_mul (mul_pos (mul_pos two_pos (mem_Ioi.mp hu)) (Real.exp_pos _)).le]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (mul_pos (mul_pos two_pos (mem_Ioi.mp hu)) (Real.exp_pos _)).le (abs_nonneg _)

/-- **Heat-kernel mollification versus circle average, second moment**, with the finite
scale-free constant `V₀ = ∫_0^∞ 2u e^{-u²} |log u| du`. -/
theorem lintegral_sq_heatMollify_sub_circleAvg_le_const
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) :
    ∫⁻ ω, ENNReal.ofReal ((heatMollify ε (h ω) z - circleAvg (h ω) ε z) ^ 2) ∂P ≤
      ENNReal.ofReal heatCircleVarConst :=
  (lintegral_sq_heatMollify_sub_circleAvg_le hh hε z).trans_eq lintegral_gaussRadial_abs_log_eq

/-- **Variance of the heat-versus-circle difference.** For a whole-plane GFF normalized by
`h_1(0) = 0`, every scale `ε > 0` and every centre `z`, the random variable `h*_ε(z) - h_ε(z)` has
a centered Gaussian law `N(0, V)` with `V ≤ ∫_0^∞ 2u e^{-u²} |log u| du`. -/
theorem exists_gaussianReal_heatMollify_sub_circleAvg_le
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) :
    ∃ V : NNReal,
      P.map (fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z) = gaussianReal 0 V ∧
        (V : ℝ) ≤ heatCircleVarConst := by
  have := hh.1.gaussian.isProbabilityMeasure
  obtain ⟨V, hV⟩ := exists_gaussianReal_heatMollify_sub_circleAvg hh.1 hε z
  refine ⟨V, hV, ?_⟩
  have h1 := lintegral_sq_heatMollify_sub_circleAvg_le_const hh hε z
  rw [lintegral_sq_eq_of_map_eq_gaussianReal (measurable_heatMollify_sub_circleAvg hh.1 ε z)
    hV] at h1
  exact (ENNReal.ofReal_le_ofReal_iff heatCircleVarConst_nonneg).1 h1

/-- The constant `V₀ = ∫_0^∞ 2u e^{-u²} |log u| du` is positive: the integrand is positive on `(2, 3)`. -/
lemma heatCircleVarConst_pos : 0 < heatCircleVarConst := by
  unfold heatCircleVarConst
  rw [setIntegral_pos_iff_support_of_nonneg_ae _ integrableOn_gaussRadial_abs_log]
  · have hsub : Ioo (2 : ℝ) 3 ⊆ Function.support
        (fun u : ℝ => 2 * u * Real.exp (-u ^ 2) * |Real.log u|) ∩ Ioi 0 := by
      intro u hu
      have hu0 : (0 : ℝ) < u := by linarith [hu.1]
      refine ⟨?_, hu0⟩
      have hlog : 0 < Real.log u := Real.log_pos (by linarith [hu.1])
      exact (mul_pos (mul_pos (mul_pos two_pos hu0) (Real.exp_pos _))
        (abs_pos.mpr hlog.ne')).ne'
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioo]
    norm_num
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (mul_pos (mul_pos two_pos (mem_Ioi.mp hu)) (Real.exp_pos _)).le
      (abs_nonneg _)

/-- **Gaussian tail of the heat-versus-circle difference.** For a whole-plane GFF normalized by
`h_1(0) = 0`, every scale `ε > 0`, every centre `z` and every level `T > 0`,
`P(|h*_ε(z) - h_ε(z)| ≥ T) ≤ 2 exp(-T² / (2 V₀))` with `V₀ = ∫_0^∞ 2u e^{-u²} |log u| du`. -/
theorem measure_abs_heatMollify_sub_circleAvg_ge_le
    (hh : SupercriticalLQGUniqueness.IsNormalizedWholePlaneGFF h P) {ε : ℝ} (hε : 0 < ε)
    (z : ℂ) {T : ℝ} (hT : 0 < T) :
    P {ω | T ≤ |heatMollify ε (h ω) z - circleAvg (h ω) ε z|} ≤
      ENNReal.ofReal (2 * Real.exp (-(T ^ 2 / (2 * heatCircleVarConst)))) := by
  obtain ⟨V, hV, hVle⟩ := exists_gaussianReal_heatMollify_sub_circleAvg_le hh hε z
  have hR := measurable_heatMollify_sub_circleAvg hh.1 ε z
  have hS : MeasurableSet {x : ℝ | T ≤ |x|} := measurableSet_le measurable_const measurable_id.abs
  have hpre : {ω | T ≤ |heatMollify ε (h ω) z - circleAvg (h ω) ε z|} =
      (fun ω => heatMollify ε (h ω) z - circleAvg (h ω) ε z) ⁻¹' {x : ℝ | T ≤ |x|} := rfl
  rw [hpre, ← Measure.map_apply hR hS, hV]
  exact LatticeProb.Isonormal.gaussianReal_abs_ge_le V heatCircleVarConst hVle
    heatCircleVarConst_pos T hT

end LQGMetric.HeatCircle
