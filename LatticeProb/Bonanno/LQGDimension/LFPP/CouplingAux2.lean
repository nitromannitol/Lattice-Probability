/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.CouplingAux2 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1

/-!
# Node `C36`, auxiliary file 2: logarithmic energies of circles and the heat representation

* `lPair μ ν = ∫∫ log|x - y| dμ dν`; for circle measures it is computed by the circle average
  of `log|x - ·|` (`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog`).
* `circ_heatRep`: `∫_0^∞ (gPair t σ σ' - e^{-1/(4t²)}) dt/t = -lPair σ σ'` for circle measures.
* `gffCircleCov_eq_lPair`: the circle-average covariance of the normalised GFF in terms of
  `lPair` against the unit circle.
* `selfPair_bound`: `∫_0^R gPair t σ σ dt/t ≤ 2R²/r² + r²/(2R²)` for a circle of radius `r`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace

namespace LQGDimension.Coupling

open HeatKernel

/-! ## 1. Log-integrability on circles -/

lemma integrable_log_norm_sub_circ (x c : ℂ) (r : ℝ) :
    Integrable (fun y => Real.log ‖x - y‖) (circMeas c r) := by
  have hm : Measurable fun y : ℂ => Real.log ‖x - y‖ := by fun_prop
  rw [circMeas, integrable_map_measure hm.aestronglyMeasurable
    (continuous_circleMap c r).aemeasurable]
  have h := circleIntegrable_log_norm_sub_const (a := x) (c := c) r
  rw [circleIntegrable_def, intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)] at h
  have h2 : (ENNReal.ofReal (2 * π))⁻¹ ≠ ⊤ := by
    rw [ENNReal.inv_ne_top]; simp [Real.pi_pos]
  refine (Integrable.smul_measure h h2).congr (ae_of_all _ fun θ => ?_)
  simp only [Function.comp_apply]
  rw [norm_sub_rev]

lemma integrable_posLog_norm_circ (c : ℂ) (r : ℝ) :
    Integrable (fun x => log⁺ ‖x‖) (circMeas c r) := by
  refine Integrable.of_bound (by fun_prop) (‖c‖ + |r|) ?_
  filter_upwards [ae_circMeas c r] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg posLog_nonneg]
  refine (posLog_le_abs _).trans ?_
  rw [abs_norm]
  calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
    _ = ‖c‖ + |r| := by rw [hx]; ring

lemma norm_le_of_circ {x c : ℂ} {r : ℝ} (hx : ‖x - c‖ = |r|) : ‖x‖ ≤ ‖c‖ + |r| := by
  calc ‖x‖ = ‖(x - c) + c‖ := by rw [sub_add_cancel]
    _ ≤ ‖x - c‖ + ‖c‖ := norm_add_le _ _
    _ = ‖c‖ + |r| := by rw [hx]; ring

lemma integral_log_norm_sub_circ (x c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ y, Real.log ‖x - y‖ ∂circMeas c r = Real.log r + log⁺ (r⁻¹ * ‖c - x‖) := by
  have hm : Measurable fun y : ℂ => Real.log ‖x - y‖ := by fun_prop
  rw [integral_circMeas_eq_circleAverage hm.aestronglyMeasurable]
  have : (fun y : ℂ => Real.log ‖x - y‖) = (Real.log ‖· - x‖) := by
    funext y; rw [norm_sub_rev]
  rw [this, circleAverage_log_norm_sub_const_eq_log_radius_add_posLog hr.ne']

lemma integral_abs_log_le (x c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ y, |Real.log ‖x - y‖| ∂circMeas c r ≤ 2 * (‖x‖ + ‖c‖ + r) - Real.log r := by
  have hi := integrable_log_norm_sub_circ x c r
  have hpfun : (fun y => log⁺ ‖x - y‖) =
      fun y => 2⁻¹ * (Real.log ‖x - y‖ + |Real.log ‖x - y‖|) := by
    funext y; exact half_mul_log_add_log_abs.symm
  have hp : Integrable (fun y => log⁺ ‖x - y‖) (circMeas c r) := by
    rw [hpfun]; exact (hi.add hi.abs).const_mul _
  have heq : (fun y => |Real.log ‖x - y‖|) =
      fun y => 2 * log⁺ ‖x - y‖ - Real.log ‖x - y‖ := by
    funext y
    have := half_mul_log_add_log_abs (x := ‖x - y‖)
    linarith
  have hbd : ∫ y, log⁺ ‖x - y‖ ∂circMeas c r ≤ ‖x‖ + ‖c‖ + r := by
    have : ∫ y, log⁺ ‖x - y‖ ∂circMeas c r ≤ ∫ _y, (‖x‖ + ‖c‖ + r) ∂circMeas c r := by
      refine integral_mono_ae hp (integrable_const _) ?_
      filter_upwards [ae_circMeas c r] with y hy
      refine (posLog_le_abs _).trans ?_
      rw [abs_norm]
      have := norm_le_of_circ hy
      rw [abs_of_pos hr] at this
      calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
        _ ≤ ‖x‖ + ‖c‖ + r := by linarith
    simpa using this
  rw [heq, integral_sub (hp.const_mul 2) hi, integral_const_mul,
    integral_log_norm_sub_circ x c hr]
  have := posLog_nonneg (x := r⁻¹ * ‖c - x‖)
  linarith

/-- `log|x - y|` is integrable for the product of two circle measures. -/
lemma integrable_log_circ_prod (c c' : ℂ) (r : ℝ) {r' : ℝ} (hr' : 0 < r') :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      ((circMeas c r).prod (circMeas c' r')) := by
  have hm : AEStronglyMeasurable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      ((circMeas c r).prod (circMeas c' r')) :=
    (by fun_prop : Measurable fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖).aestronglyMeasurable
  rw [integrable_prod_iff hm]
  refine ⟨ae_of_all _ fun x => integrable_log_norm_sub_circ x c' r', ?_⟩
  refine Integrable.of_bound hm.norm.integral_prod_right'
    (2 * (‖c‖ + |r| + ‖c'‖ + r') - Real.log r') ?_
  filter_upwards [ae_circMeas c r] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simp only [Real.norm_eq_abs]
  refine (integral_abs_log_le x c' hr').trans ?_
  have := norm_le_of_circ hx
  linarith

/-! ## 2. Logarithmic pairings -/

/-- The logarithmic pairing `∫∫ log|x - y| dμ(x) dν(y)`. -/
def lPair (μ ν : Measure ℂ) : ℝ := ∫ p, Real.log ‖p.1 - p.2‖ ∂(μ.prod ν)

lemma lPair_circ (c c' : ℂ) (r : ℝ) {r' : ℝ} (hr' : 0 < r') :
    lPair (circMeas c r) (circMeas c' r') =
      ∫ x, (Real.log r' + log⁺ (r'⁻¹ * ‖c' - x‖)) ∂circMeas c r := by
  rw [lPair, integral_prod _ (integrable_log_circ_prod c c' r hr')]
  congr 1
  funext x
  exact integral_log_norm_sub_circ x c' hr'

lemma lPair_self (c : ℂ) {r : ℝ} (hr : 0 < r) :
    lPair (circMeas c r) (circMeas c r) = Real.log r := by
  rw [lPair_circ c c r hr]
  have : ∀ᵐ x ∂circMeas c r, Real.log r + log⁺ (r⁻¹ * ‖c - x‖) = Real.log r := by
    filter_upwards [ae_circMeas c r] with x hx
    rw [norm_sub_rev, hx, abs_of_pos hr, inv_mul_cancel₀ hr.ne', posLog_one, add_zero]
  rw [integral_congr_ae this]
  simp

lemma lPair_unit_right (c : ℂ) (r : ℝ) :
    lPair (circMeas c r) (circMeas 0 1) = ∫ x, log⁺ ‖x‖ ∂circMeas c r := by
  rw [lPair_circ c 0 r one_pos]
  simp

lemma lPair_unit_left (c : ℂ) {r : ℝ} (hr : 0 < r) :
    lPair (circMeas 0 1) (circMeas c r) = ∫ y, log⁺ ‖y‖ ∂circMeas c r := by
  rw [lPair, integral_prod_symm _ (integrable_log_circ_prod 0 c 1 hr)]
  congr 1
  funext y
  simp only
  have : (fun x : ℂ => Real.log ‖x - y‖) = fun x => Real.log ‖y - x‖ := by
    funext x; rw [norm_sub_rev]
  rw [this, integral_log_norm_sub_circ y 0 one_pos]
  simp

lemma lPair_unit_unit : lPair (circMeas 0 1) (circMeas 0 1) = 0 := by
  rw [lPair_self 0 one_pos, Real.log_one]

/-! ## 3. Heat-kernel representation for circles -/

/-- **Heat-kernel representation for two circles.** -/
theorem circ_heatRep (c c' : ℂ) (r : ℝ) {r' : ℝ} (hr' : 0 < r') :
    IntegrableOn (fun t => (gPair t (circMeas c r) (circMeas c' r') -
        Real.exp (-1 / (4 * t ^ 2))) / t) (Ioi 0) ∧
    ∫ t in Ioi 0, (gPair t (circMeas c r) (circMeas c' r') - Real.exp (-1 / (4 * t ^ 2))) / t =
      -lPair (circMeas c r) (circMeas c' r') := by
  obtain ⟨h1, h2⟩ := heatRep_of_integrable_log ((circMeas c r).prod (circMeas c' r'))
    (fun p => ‖p.1 - p.2‖) (by fun_prop) (ae_ne_circMeas_prod c c' r hr'.ne')
    (integrable_log_circ_prod c c' r hr')
  simp only [probReal_univ, one_mul] at h1 h2
  have hfun : ∀ t, gPair t (circMeas c r) (circMeas c' r') =
      ∫ p, Real.exp (-‖p.1 - p.2‖ ^ 2 / (4 * t ^ 2)) ∂((circMeas c r).prod (circMeas c' r')) :=
    fun t => gPair_eq_prod t _ _
  simp_rw [hfun]
  exact ⟨h1, h2⟩

/-! ## 4. The circle-average covariance -/

lemma measurable_gffGreen : Measurable fun p : ℂ × ℂ => gffGreen p.1 p.2 := by
  unfold gffGreen; fun_prop

lemma gffCircleCov_eq_integral (z w : ℂ) (ε δ : ℝ) :
    gffCircleCov ε z δ w = ∫ x, ∫ y, gffGreen x y ∂circMeas w δ ∂circMeas z ε := by
  have hF : AEStronglyMeasurable (fun x => ∫ y, gffGreen x y ∂circMeas w δ) (circMeas z ε) :=
    (measurable_gffGreen.stronglyMeasurable.integral_prod_right' (ν := circMeas w δ)
      ).aestronglyMeasurable
  rw [integral_circMeas' hF]
  have hin : ∀ θ : ℝ, ∫ y, gffGreen (circleMap z ε θ) y ∂circMeas w δ =
      (2 * π)⁻¹ * ∫ φ in (0 : ℝ)..2 * π, gffGreen (circleMap z ε θ) (circleMap w δ φ) := by
    intro θ
    refine integral_circMeas' ?_
    exact (measurable_gffGreen.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  simp_rw [hin]
  rw [intervalIntegral.integral_const_mul, gffCircleCov]
  simp only [circleMap]
  ring

/-- **The GFF circle-average covariance in terms of logarithmic pairings.** -/
theorem gffCircleCov_eq_lPair (s s' : ℂ) {ε : ℝ} (hε : 0 < ε) :
    gffCircleCov ε s ε s' = -lPair (circMeas s ε) (circMeas s' ε) +
      lPair (circMeas s ε) (circMeas 0 1) + lPair (circMeas 0 1) (circMeas s' ε) -
        lPair (circMeas 0 1) (circMeas 0 1) := by
  rw [gffCircleCov_eq_integral, lPair_unit_right, lPair_unit_left s' hε, lPair_unit_unit,
    sub_zero]
  have hL := integrable_log_circ_prod s s' ε hε
  have hPx := integrable_posLog_norm_circ s ε
  have hPy := integrable_posLog_norm_circ s' ε
  have hG : ∀ x y : ℂ, gffGreen x y = -Real.log ‖x - y‖ + log⁺ ‖x‖ + log⁺ ‖y‖ := by
    intro x y
    rw [gffGreen, posLog_eq_log_max_one (norm_nonneg x), posLog_eq_log_max_one (norm_nonneg y),
      max_comm 1 ‖x‖, max_comm 1 ‖y‖]
  have hin : ∀ x : ℂ, ∫ y, gffGreen x y ∂circMeas s' ε =
      -∫ y, Real.log ‖x - y‖ ∂circMeas s' ε + log⁺ ‖x‖ + ∫ y, log⁺ ‖y‖ ∂circMeas s' ε := by
    intro x
    simp_rw [hG x]
    have h1 : Integrable (fun y => -Real.log ‖x - y‖) (circMeas s' ε) :=
      (integrable_log_norm_sub_circ x s' ε).neg
    have h2 : Integrable (fun y => -Real.log ‖x - y‖ + log⁺ ‖x‖) (circMeas s' ε) :=
      h1.add (integrable_const _)
    rw [integral_add h2 hPy, integral_add h1 (integrable_const _), integral_neg]
    simp
  simp_rw [hin]
  have hI : Integrable (fun x => ∫ y, Real.log ‖x - y‖ ∂circMeas s' ε) (circMeas s ε) :=
    hL.integral_prod_left
  have k1 : Integrable (fun x => -∫ y, Real.log ‖x - y‖ ∂circMeas s' ε) (circMeas s ε) :=
    hI.neg
  have k2 : Integrable (fun x => -∫ y, Real.log ‖x - y‖ ∂circMeas s' ε + log⁺ ‖x‖)
      (circMeas s ε) := k1.add hPx
  rw [integral_add k2 (integrable_const _), integral_add k1 hPx, integral_neg,
    lPair, integral_prod _ hL]
  simp

/-! ## 5. Elementary bounds -/

lemma abs_gK_sub_exp_le (t : ℝ) (x y : ℂ) (r : ℝ) :
    |gK t x y - Real.exp (-r ^ 2 / (4 * t ^ 2))| ≤ |‖x - y‖ ^ 2 - r ^ 2| / (4 * t ^ 2) := by
  have hD : 0 ≤ 4 * t ^ 2 := by positivity
  refine (abs_exp_sub_exp_le_of_nonpos ?_ ?_).trans (le_of_eq ?_)
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hD
  · exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) hD
  · rw [show -‖x - y‖ ^ 2 / (4 * t ^ 2) - -r ^ 2 / (4 * t ^ 2) =
        -(‖x - y‖ ^ 2 - r ^ 2) / (4 * t ^ 2) by ring, abs_div, abs_neg, abs_of_nonneg hD]

/-- Deviation of `gPair` from a constant, controlled by a.e. properties of the two measures. -/
lemma abs_gPair_sub_le {t a M : ℝ} {μ ν : Measure ℂ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {P Q : ℂ → Prop} (hP : ∀ᵐ x ∂μ, P x) (hQ : ∀ᵐ y ∂ν, Q y)
    (h : ∀ x y, P x → Q y → |gK t x y - a| ≤ M) : |gPair t μ ν - a| ≤ M := by
  have hin : ∀ x, ∫ y, gK t x y ∂ν - a = ∫ y, (gK t x y - a) ∂ν := by
    intro x
    have hi : Integrable (fun y => gK t x y) ν := integrable_gK ν t measurable_const measurable_id
    rw [integral_sub hi (integrable_const a)]
    simp
  have hI : Integrable (fun x => ∫ y, gK t x y ∂ν) μ :=
    (integrable_gK (μ.prod ν) t measurable_fst measurable_snd).integral_prod_left
  have hout : gPair t μ ν - a = ∫ x, (∫ y, gK t x y ∂ν - a) ∂μ := by
    rw [integral_sub hI (integrable_const a), gPair]
    simp
  rw [hout, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := M) ?_).trans (by simp)
  filter_upwards [hP] with x hx
  rw [hin x]
  refine (norm_integral_le_of_norm_le_const (C := M) ?_).trans (by simp)
  filter_upwards [hQ] with y hy
  rw [Real.norm_eq_abs]
  exact h x y hx hy

lemma integrableOn_inv_pow_three {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => (t ^ 3)⁻¹) (Ioi R) := by
  refine (integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hR).congr_fun
    (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 < t := lt_trans hR ht
  show t ^ (-3 : ℝ) = (t ^ 3)⁻¹
  rw [Real.rpow_neg ht0.le]; norm_num

lemma integral_inv_pow_three {R : ℝ} (hR : 0 < R) :
    ∫ t in Ioi R, (t ^ 3)⁻¹ = (2 * R ^ 2)⁻¹ := by
  have h := integral_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) hR
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun t : ℝ => (t ^ 3)⁻¹)
    (fun t ht => by
      have ht0 : 0 < t := lt_trans hR ht
      simp only
      rw [Real.rpow_neg ht0.le]; norm_num)] at h
  rw [h, show (-3 : ℝ) + 1 = -2 by norm_num, Real.rpow_neg hR.le]
  norm_num
  ring

/-! ## 6. Small-scale bound for the self-pairing of a circle -/

/-- `∫_0^R gPair t σ σ dt/t ≤ 2R²/r² + r²/(2R²)` for the circle `σ` of radius `r`. -/
theorem selfPair_bound (c : ℂ) {r R : ℝ} (hr : 0 < r) (hR : 0 < R) :
    IntegrableOn (fun t => gPair t (circMeas c r) (circMeas c r) / t) (Ioc 0 R) ∧
    ∫ t in Ioc 0 R, gPair t (circMeas c r) (circMeas c r) / t ≤
      2 * R ^ 2 / r ^ 2 + r ^ 2 / (2 * R ^ 2) := by
  set σ := circMeas c r with hσ
  set G : ℝ → ℝ := fun t => gPair t σ σ with hG
  set er : ℝ → ℝ := fun t => Real.exp (-r ^ 2 / (4 * t ^ 2)) with her
  set E : ℝ → ℝ := fun t => (G t - er t) / t with hE
  obtain ⟨hH1, hH2⟩ := circ_heatRep c c r hr
  have hEeq : E = fun t => (G t - Real.exp (-1 / (4 * t ^ 2))) / t - frIntegrand r t := by
    funext t; simp only [hE, hG, her, frIntegrand]; ring
  have hEint : IntegrableOn E (Ioi 0) := by
    rw [hEeq]; exact hH1.sub (frIntegrand_integrableOn hr)
  have hEzero : ∫ t in Ioi 0, E t = 0 := by
    rw [hEeq, integral_sub hH1 (frIntegrand_integrableOn hr), hH2, frIntegrand_integral hr,
      lPair_self c hr]
    ring
  have hsplit : ∫ t in Ioi 0, E t = (∫ t in Ioc 0 R, E t) + ∫ t in Ioi R, E t := by
    rw [← Ioc_union_Ioi_eq_Ioi hR.le]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hEint.mono_set Ioc_subset_Ioi_self) (hEint.mono_set (Ioi_subset_Ioi hR.le))
  -- the tail bound `-E t ≤ r² t⁻³`
  have htail : ∀ t ∈ Ioi R, -E t ≤ r ^ 2 * (t ^ 3)⁻¹ := by
    intro t ht
    have ht0 : 0 < t := lt_trans hR ht
    have hb : |G t - er t| ≤ r ^ 2 / t ^ 2 := by
      refine abs_gPair_sub_le (ae_circMeas c r) (ae_circMeas c r) fun x y hx hy => ?_
      refine (abs_gK_sub_exp_le t x y r).trans ?_
      rw [abs_of_pos hr] at hx hy
      have hxy : ‖x - y‖ ≤ 2 * r := by
        calc ‖x - y‖ = ‖(x - c) - (y - c)‖ := by congr 1; ring
          _ ≤ ‖x - c‖ + ‖y - c‖ := norm_sub_le _ _
          _ = 2 * r := by rw [hx, hy]; ring
      have h1 : |‖x - y‖ ^ 2 - r ^ 2| ≤ 4 * r ^ 2 := by
        rw [abs_le]
        constructor
        · nlinarith [norm_nonneg (x - y)]
        · nlinarith [norm_nonneg (x - y)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg t]
    have : -E t = (er t - G t) / t := by simp only [hE]; ring
    rw [this]
    calc (er t - G t) / t ≤ (r ^ 2 / t ^ 2) / t := by
          refine div_le_div_of_nonneg_right ?_ ht0.le
          have := neg_abs_le (G t - er t)
          linarith
      _ = r ^ 2 * (t ^ 3)⁻¹ := by field_simp
  have htailInt : ∫ t in Ioi R, -E t ≤ r ^ 2 / (2 * R ^ 2) := by
    calc ∫ t in Ioi R, -E t ≤ ∫ t in Ioi R, r ^ 2 * (t ^ 3)⁻¹ :=
          setIntegral_mono_on (hEint.mono_set (Ioi_subset_Ioi hR.le)).neg
            ((integrableOn_inv_pow_three hR).const_mul _) measurableSet_Ioi htail
      _ = r ^ 2 / (2 * R ^ 2) := by
          rw [integral_const_mul, integral_inv_pow_three hR]; ring
  -- the main term `e^{-r²/(4t²)}/t ≤ 4t/r²`
  have hmain : ∀ t ∈ Ioc 0 R, er t / t ≤ 4 / r ^ 2 * t := by
    intro t ht
    have ht0 : 0 < t := ht.1
    have := exp_neg_div_four_sq_le (pow_pos hr 2) ht0.ne'
    rw [div_le_iff₀ ht0]
    calc er t ≤ 4 * t ^ 2 / r ^ 2 := this
      _ = 4 / r ^ 2 * t * t := by ring
  have hmeas_er : Measurable fun t => er t / t := by simp only [her]; fun_prop
  have herInt : IntegrableOn (fun t => er t / t) (Ioc 0 R) := by
    refine IntegrableOn.of_bound (by simp [Real.volume_Ioc]) hmeas_er.aestronglyMeasurable
      (4 / r ^ 2 * R) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.exp_pos _).le ht.1.le)]
    refine (hmain t ht).trans ?_
    gcongr
    exact ht.2
  have hlinInt : IntegrableOn (fun t : ℝ => 4 / r ^ 2 * t) (Ioc 0 R) :=
    (continuous_const.mul continuous_id).integrableOn_Ioc
  have herBound : ∫ t in Ioc 0 R, er t / t ≤ 2 * R ^ 2 / r ^ 2 := by
    calc ∫ t in Ioc 0 R, er t / t ≤ ∫ t in Ioc 0 R, 4 / r ^ 2 * t :=
          setIntegral_mono_on herInt hlinInt measurableSet_Ioc hmain
      _ = 2 * R ^ 2 / r ^ 2 := by
          rw [integral_const_mul, ← intervalIntegral.integral_of_le hR.le, integral_id]
          ring
  have hGeq : (fun t => G t / t) = fun t => er t / t + E t := by
    funext t; simp only [hE]; ring
  have hEIoc : IntegrableOn E (Ioc 0 R) := hEint.mono_set Ioc_subset_Ioi_self
  refine ⟨?_, ?_⟩
  · show IntegrableOn (fun t => G t / t) (Ioc 0 R)
    rw [hGeq]; exact herInt.add hEIoc
  · show ∫ t in Ioc 0 R, G t / t ≤ _
    rw [hGeq, integral_add herInt hEIoc]
    have h1 : ∫ t in Ioc 0 R, E t = -∫ t in Ioi R, E t := by linarith
    rw [h1, ← integral_neg]
    linarith

end LQGDimension.Coupling
