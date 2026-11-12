/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.BallMoment at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.BallIndep
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.GMCInterfaces
import LatticeProb.Bonanno.LQGMetric.Papers.DG.Lemma25Gauss

/-!
# Moments of the LQG mass of small balls at the origin

For a whole-plane GFF circle-average process `H` normalized by `h_1(0) = 0` (measurable coordinates) with LQG measure
`μ` (`IsLQGAreaOf`), `0 < γ < 2` and `0 < q < 4/γ²`:

  `E[μ(B_ρ(0))^q] ≤ C ρ^{q(2+γ²/2) − q²γ²/2}` for `0 < ρ ≤ 1/64` (`exists_lintegral_ball_origin_rpow_le`).

This is the multifractal scaling of GMC at a fixed point ([16] , (A.4)–(A.6) with `α = 0`):
the factorization of `BallIndep.lean` (`E μ_k(Q)^q = ε^{q(2+γ²/2) − q²γ²/2} E S_k^q`, `ε = 32ρ`), `E S_k^q ≤ 1` for
`q ≤ 1` (Jensen; `E S_k ≤ 1/4`) and `E S_k^q ≤ C` for `1 < q < 4/γ²` (`PosMoment.lean`), and Fatou along the vague
convergence with a plateau test function.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Finset Filter Topology
open LQGMetric.DGMC LQGMetric.DGMC.Neg3 LQGMetric.CircleAvg
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMCFacts

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {H : ℝ → ℂ → Ω → ℝ}

/-- Jensen for `x ↦ x^q`, `0 < q ≤ 1`, on a probability space, in `ℝ≥0∞`. -/
lemma lintegral_rpow_le_rpow_lintegral_of_le_one [IsProbabilityMeasure P] {f : Ω → ℝ≥0∞}
    (hf : AEMeasurable f P) {q : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1) :
    ∫⁻ ω, f ω ^ q ∂P ≤ (∫⁻ ω, f ω ∂P) ^ q := by
  rcases hq1.lt_or_eq with hq1 | rfl
  · have hpq : (1 / q).HolderConjugate (1 / (1 - q)) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [one_div, one_div, inv_inv, inv_inv]; ring
      · rw [one_div]; exact inv_pos.2 hq0
      · rw [one_div]; exact inv_pos.2 (by linarith)
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq (hf.pow_const q) aemeasurable_const
      (g := fun _ => 1)
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
    refine h.trans (le_of_eq ?_)
    rw [one_div_one_div]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
  · simp

/-- The recentred density has mean one: `E[(r/ε)^{γ²/2} e^{γ(h_r(w) − h_ε(z))}] = 1` (`|w − z| ≤ ε/2`, `r ≤ ε/2`). -/
lemma lintegral_nDens_eq_one (hH : LQGDimension.IsGFFCircleAverage H P) (γ : ℝ) (z : ℂ) {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε / 2) {w : ℂ} (hw : ‖w - z‖ ≤ ε / 2) :
    ∫⁻ ω, nDens γ H z ε r w ω ∂P = 1 := by
  have hP := hH.isProbabilityMeasure
  have hg : HasGaussianLaw (fun ω => γ * (H r w ω - H ε z ω)) P :=
    (isGaussianProcess_recentred hH γ hε z (fun _ : Unit => r) (fun _ => hr)
      (fun _ => w)).hasGaussianLaw_eval ()
  obtain ⟨hi, he⟩ := integral_exp_mul_of_hasGaussianLaw hg (integral_recentred hH γ hε hr z w) 1
  have hvar : Var[fun ω => γ * (H r w ω - H ε z ω); P] = γ ^ 2 * (Real.log ε - Real.log r) := by
    rw [← covariance_self hg.aemeasurable, covariance_const_mul_left, covariance_const_mul_right,
      cov_recentred_self hH hε hr hrε hw]
    ring
  have e : ∀ ω, nDens γ H z ε r w ω = ENNReal.ofReal ((r / ε) ^ (γ ^ 2 / 2)) *
      ENNReal.ofReal (Real.exp (1 * (γ * (H r w ω - H ε z ω)))) := fun ω => by
    rw [nDens, one_mul, ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hr hε).le _)]
  simp_rw [e]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun ω => (Real.exp_pos _).le), he, hvar,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg (div_pos hr hε).le _), ← ENNReal.ofReal_one]
  congr 1
  rw [Real.div_rpow hr.le hε.le, Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hε, ← Real.exp_sub,
    ← Real.exp_add]
  convert Real.exp_zero using 2
  ring

/-- `E S_k ≤ 1/4`. -/
lemma lintegral_sMass_le (hH : LQGDimension.IsGFFCircleAverage H P) (hHm : ∀ r z, Measurable (H r z))
    (γ : ℝ) {ε : ℝ} (hε : 0 < ε) {m : ℕ} (ha : QuantumZipper.radius m ≤ ε / 2) (k : ℕ) :
    ∫⁻ ω, sMass γ H ε m k ω ∂P ≤ 1 := by
  have hP := hH.isProbabilityMeasure
  set a := QuantumZipper.radius m with ha_def
  set r := QuantumZipper.radius (m + k)
  have hr : 0 < r := QuantumZipper.radius_pos _
  have hra : r ≤ a := by
    simp only [r, a]
    rw [radius_add]
    exact mul_le_of_le_one_right (QuantumZipper.radius_pos m).le
      (pow_le_one₀ (by norm_num) (by norm_num))
  set Q := sqQ (sqCorner 0 a) m
  have hjm := measurable_uncurry_coord hH hHm hr
  have hd : Measurable fun p : ℂ × Ω => nDens γ H 0 ε r p.1 p.2 :=
    ENNReal.measurable_ofReal.comp (((hjm.sub ((hHm ε 0).comp measurable_snd)).const_mul
      γ).exp.const_mul _)
  simp only [sMass]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rw [lintegral_lintegral_swap (μ := P) (ν := volume.restrict Q)
    (f := fun ω w => nDens γ H 0 ε r w ω) (hd.comp (measurable_snd.prodMk measurable_fst)).aemeasurable]
  have hone : ∀ w ∈ Q, ∫⁻ ω, nDens γ H 0 ε r w ω ∂P = 1 := fun w hw =>
    lintegral_nDens_eq_one hH γ 0 hε hr (hra.trans ha)
      (by rw [sub_zero]; exact (mem_sqQ_norm_le ha_def hw).trans ha)
  rw [setLIntegral_congr_fun (measurableSet_sqQ _ _) hone, setLIntegral_const, one_mul]
  have hvol : volume Q = ENNReal.ofReal (a ^ 2) := by
    have := lintegral_sqQ (fun _ => (1 : ℝ≥0∞)) measurable_const (sqCorner 0 a) m
    rw [setLIntegral_const, one_mul, setLIntegral_const, one_mul, volume_cell0, mul_one] at this
    exact this
  rw [hvol, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_one]
  rw [inv_pow, inv_mul_le_iff₀ (by positivity), mul_one]
  nlinarith [QuantumZipper.radius_pos m]

lemma measurable_sMass (hH : LQGDimension.IsGFFCircleAverage H P) (hHm : ∀ r z, Measurable (H r z))
    (γ ε : ℝ) (m k : ℕ) : Measurable (sMass γ H ε m k) := by
  have hr : 0 < QuantumZipper.radius (m + k) := QuantumZipper.radius_pos _
  have hjm := measurable_uncurry_coord hH hHm hr
  have hd : Measurable fun p : ℂ × Ω => nDens γ H 0 ε (QuantumZipper.radius (m + k)) p.1 p.2 :=
    ENNReal.measurable_ofReal.comp (((hjm.sub ((hHm ε 0).comp measurable_snd)).const_mul
      γ).exp.const_mul _)
  exact hd.lintegral_prod_left'.const_mul _

/-- **Uniform moments of the normalized recentred mass**, `0 < q < 4/γ²`. -/
theorem exists_lintegral_sMass_rpow_le (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ q : ℝ} (hγ : 0 < γ) (hq0 : 0 < q) (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (ε : ℝ) (m k : ℕ), 0 < ε → QuantumZipper.radius m ≤ ε / 2 →
      ε / 8 < QuantumZipper.radius m → ∫⁻ ω, sMass γ H ε m k ω ^ q ∂P ≤ C := by
  have hP := hH.isProbabilityMeasure
  rcases le_or_gt q 1 with hq1 | hq1
  · refine ⟨1, ENNReal.one_lt_top, fun ε m k hε ha _ => ?_⟩
    calc ∫⁻ ω, sMass γ H ε m k ω ^ q ∂P ≤ (∫⁻ ω, sMass γ H ε m k ω ∂P) ^ q :=
          lintegral_rpow_le_rpow_lintegral_of_le_one (measurable_sMass hH hHm γ ε m k).aemeasurable
            hq0 hq1
      _ ≤ 1 ^ q := ENNReal.rpow_le_rpow (lintegral_sMass_le hH hHm γ hε ha k) hq0.le
      _ = 1 := ENNReal.one_rpow q
  · obtain ⟨C, hC, h⟩ := exists_lintegral_sq_rpow_le_pos hH hHm hγ hq1 hq
    exact ⟨C, hC, fun ε m k hε ha ha' => h 0 ε m k hε ha ha'⟩

/-- **Moments of the LQG mass of small balls at the origin**: `E μ(B_ρ(0))^q ≤ C ρ^{q(2+γ²/2) − q²γ²/2}`. -/
theorem exists_lintegral_ball_origin_rpow_le (hH : LQGDimension.IsGFFCircleAverage H P)
    (hHm : ∀ r z, Measurable (H r z)) {γ : ℝ} (hγ : 0 < γ) {μ : Ω → Measure ℂ}
    (hμ : GMSLemma27.IsLQGAreaOf γ H μ P) {q : ℝ} (hq0 : 0 < q) (hq : q < 4 / γ ^ 2) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 / 64 →
      ∫⁻ ω, μ ω (ball 0 ρ) ^ q ∂P ≤
        C * ENNReal.ofReal (ρ ^ (q * (2 + γ ^ 2 / 2) - q ^ 2 * γ ^ 2 / 2)) := by
  have hP := hH.isProbabilityMeasure
  obtain ⟨C₀, hC₀, hS⟩ := exists_lintegral_sMass_rpow_le hH hHm hγ hq0 hq
  set e := q * (2 + γ ^ 2 / 2) - q ^ 2 * γ ^ 2 / 2
  refine ⟨ENNReal.ofReal ((32 : ℝ) ^ e) * C₀, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC₀,
    fun ρ hρ hρ64 => ?_⟩
  set ε := 32 * ρ
  have hε : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by linarith
  obtain ⟨m, ha4, ha'⟩ := exists_radius_mem hε (by linarith)
  set a := QuantumZipper.radius m with ha_def
  have ha : a ≤ ε / 2 := ha4.trans (by linarith)
  have h4 : 0 < 4 * ρ := by positivity
  set f : ℂ → ℝ := plat 0 (4 * ρ)
  have hfc : Continuous f := continuous_plat _ _
  have hfs : HasCompactSupport f :=
    (isCompact_closedBall 0 (4 * ρ / 2)).of_isClosed_subset (isClosed_tsupport _) (tsupport_plat h4)
  set Q := sqQ (sqCorner 0 a) m
  -- `closedBall 0 (2ρ) ⊆ Q`
  have hballQ : closedBall (0 : ℂ) (2 * ρ) ⊆ Q := by
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    have hre : |w.re| ≤ 2 * ρ := (Complex.abs_re_le_norm w).trans hw
    have him : |w.im| ≤ 2 * ρ := (Complex.abs_im_le_norm w).trans hw
    have ha0 : 0 < a := QuantumZipper.radius_pos m
    have h4ρ : 4 * ρ < a := by linarith
    show (QuantumZipper.radius m)⁻¹ • (w - sqCorner 0 a) ∈ cell0
    rw [← ha_def]
    have e1 : ((a⁻¹ • (w - sqCorner 0 a)) : ℂ).re = w.re / a + 1 / 2 := by
      simp [sqCorner, sqCentre]; field_simp
    have e2 : ((a⁻¹ • (w - sqCorner 0 a)) : ℂ).im = w.im / a + 1 / 2 := by
      simp [sqCorner, sqCentre]; field_simp
    rw [abs_le] at hre him
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [e1, e2]
    · have : -(a / 2) ≤ w.re := by linarith
      have := div_le_div_of_nonneg_right this ha0.le
      rw [neg_div, div_div, mul_comm, ← div_div, div_self ha0.ne'] at this
      linarith
    · rw [show w.re / a + 1 / 2 < 1 ↔ w.re / a < 1 / 2 by constructor <;> intro h <;> linarith,
        div_lt_iff₀ ha0]
      linarith
    · have : -(a / 2) ≤ w.im := by linarith
      have := div_le_div_of_nonneg_right this ha0.le
      rw [neg_div, div_div, mul_comm, ← div_div, div_self ha0.ne'] at this
      linarith
    · rw [show w.im / a + 1 / 2 < 1 ↔ w.im / a < 1 / 2 by constructor <;> intro h <;> linarith,
        div_lt_iff₀ ha0]
      linarith
  set G : ℕ → Ω → ℝ≥0∞ := fun k ω => ∫⁻ z, ENNReal.ofReal (f z) ∂(GMSLemma27.lqgApprox γ H (m + k) ω)
  set Glim : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, ENNReal.ofReal (f z) ∂(μ ω)
  have hdr : ∀ k, 0 < GMSLemma27.dyadicRadius k := fun k => by
    rw [dyadicRadius_eq_radius]; exact QuantumZipper.radius_pos k
  have hGm : ∀ k, Measurable (G k) := fun k => by
    have hj := measurable_uncurry_coord hH hHm (hdr (m + k))
    have hjm : Measurable fun p : ℂ × Ω => ENNReal.ofReal (f p.1) * ENNReal.ofReal
        (GMSLemma27.dyadicRadius (m + k) ^ (γ ^ 2 / 2) *
          Real.exp (γ * H (GMSLemma27.dyadicRadius (m + k)) p.1 p.2)) :=
      (ENNReal.measurable_ofReal.comp (hfc.measurable.comp measurable_fst)).mul
        (ENNReal.measurable_ofReal.comp (measurable_const.mul ((hj.const_mul γ).exp)))
    have e : G k = fun ω => ∫⁻ z, ENNReal.ofReal (f z) * ENNReal.ofReal
        (GMSLemma27.dyadicRadius (m + k) ^ (γ ^ 2 / 2) *
          Real.exp (γ * H (GMSLemma27.dyadicRadius (m + k)) z ω)) := by
      funext ω
      have hcontd : Continuous fun z => H (GMSLemma27.dyadicRadius (m + k)) z ω :=
        hH.continuous _ (hdr (m + k)) ω
      have hd : Measurable fun z => ENNReal.ofReal (GMSLemma27.dyadicRadius (m + k) ^ (γ ^ 2 / 2) *
          Real.exp (γ * H (GMSLemma27.dyadicRadius (m + k)) z ω)) :=
        ENNReal.measurable_ofReal.comp
          (continuous_const.mul (continuous_const.mul hcontd).rexp).measurable
      simp only [G, GMSLemma27.lqgApprox]
      rw [lintegral_withDensity_eq_lintegral_mul₀ hd.aemeasurable
        (g := fun z => ENNReal.ofReal (f z)) (ENNReal.measurable_ofReal.comp hfc.measurable).aemeasurable]
      exact lintegral_congr fun z => by simp only [Pi.mul_apply]; exact mul_comm _ _
    rw [e]
    exact hjm.lintegral_prod_left'
  have hmk : Tendsto (fun k : ℕ => m + k) atTop atTop := by
    simpa [add_comm] using tendsto_add_atTop_nat m
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (Glim ω)) := by
    filter_upwards [hμ] with ω ⟨hlf, hc⟩
    have h1 := (ENNReal.continuous_ofReal.tendsto _).comp ((hc f hfc hfs).comp hmk)
    have e1 : ∀ k, ENNReal.ofReal (∫ z, f z ∂(GMSLemma27.lqgApprox γ H (m + k) ω)) = G k ω := fun k => by
      have := isLocallyFiniteMeasure_lqgApprox hH γ (m + k) ω
      exact ofReal_integral_plat 0 h4
    have e2 : ENNReal.ofReal (∫ z, f z ∂(μ ω)) = Glim ω := ofReal_integral_plat 0 h4
    simp only [Function.comp_def, e1, e2] at h1
    exact h1
  -- `G_k ≤ μ_k(Q)` and `μ(B_ρ) ≤ G`
  have hGQ : ∀ k ω, G k ω ≤ GMSLemma27.lqgApprox γ H (m + k) ω Q := fun k ω => by
    rw [← lintegral_indicator_one (measurableSet_sqQ _ _)]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ closedBall (0 : ℂ) (2 * ρ)
    · rw [indicator_of_mem (hballQ hz), Pi.one_apply]
      exact ENNReal.ofReal_le_one.2 (plat_le_one _ _ _)
    · rw [mem_closedBall, dist_zero_right, not_le] at hz
      rw [show f z = 0 from plat_eq_zero h4 (by rw [sub_zero]; linarith), ENNReal.ofReal_zero]
      exact zero_le
  have hballG : ∀ ω, μ ω (ball 0 ρ) ≤ Glim ω := fun ω => by
    rw [← lintegral_indicator_one measurableSet_ball]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ ball (0 : ℂ) ρ
    · rw [indicator_of_mem hz, Pi.one_apply]
      rw [mem_ball, dist_zero_right] at hz
      rw [show f z = 1 from plat_eq_one h4 (by rw [sub_zero]; linarith), ENNReal.ofReal_one]
    · rw [indicator_of_notMem hz]
      exact zero_le
  have hbound : ∀ k, ∫⁻ ω, G k ω ^ q ∂P ≤ ENNReal.ofReal (ε ^ e) * C₀ := fun k => by
    calc ∫⁻ ω, G k ω ^ q ∂P ≤ ∫⁻ ω, GMSLemma27.lqgApprox γ H (m + k) ω Q ^ q ∂P :=
          lintegral_mono fun ω => ENNReal.rpow_le_rpow (hGQ k ω) hq0.le
      _ = ENNReal.ofReal (ε ^ e) * ∫⁻ ω, sMass γ H ε m k ω ^ q ∂P :=
          lintegral_approx_sq_rpow_eq hH hHm γ hε hε1 ha k hq0
      _ ≤ ENNReal.ofReal (ε ^ e) * C₀ := by gcongr; exact hS ε m k hε ha ha'
  calc ∫⁻ ω, μ ω (ball 0 ρ) ^ q ∂P ≤ ∫⁻ ω, Glim ω ^ q ∂P :=
        lintegral_mono fun ω => ENNReal.rpow_le_rpow (hballG ω) hq0.le
    _ = ∫⁻ ω, liminf (fun k => G k ω ^ q) atTop ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hconv] with ω hω
        exact (((ENNReal.continuous_rpow_const (y := q)).tendsto _).comp hω).liminf_eq.symm
    _ ≤ liminf (fun k => ∫⁻ ω, G k ω ^ q ∂P) atTop :=
        lintegral_liminf_le fun k => (hGm k).pow_const q
    _ ≤ ENNReal.ofReal (ε ^ e) * C₀ :=
        liminf_le_of_frequently_le' (Frequently.of_forall hbound)
    _ = ENNReal.ofReal ((32 : ℝ) ^ e) * C₀ * ENNReal.ofReal (ρ ^ e) := by
        rw [Real.mul_rpow (by norm_num) hρ.le, ENNReal.ofReal_mul (by positivity)]
        ring

end MatedCRTHarmonic.GMCFacts
