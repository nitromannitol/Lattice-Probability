import LatticeProb.Gauss.CameronMartinDerived

/-!
# Cameron-Martin derivations for the whole-plane GFF

Proves the Cameron-Martin reweighting `cameronMartinGFFReweighting_derived` (for
`LatticeProb.Gauss.CameronMartinGFFReweighting`, `HarmonicBalls/LPStage/CameronMartinDerived.lean`) and the mutual
absolute continuity `cameronMartinGFFMutualAbsCont_derived` (for `LatticeProb.Gauss.CameronMartinGFFMutualAbsCont`).

The proofs are copies, with the names adapted to `LatticeProb.Gauss`, of the Harmonic-balls derivations
`FirstPass/Phase2/CameronMartinReweightingDerived.lean` (test functions, Green identity, covariance identity and the
Gaussian tilt), `FirstPass/Phase2/CameronMartinReweightingDerived2.lean` (law of the shifted family and the assembly of
`IsWholePlaneGFF`) and `FirstPass/Phase2/CameronMartinMutualDerived.lean` (mutual absolute continuity). The mathematics is
Miller-Sheffield, Imaginary Geometry IV, arXiv:1302.4738v2, Proposition 2.9, with the normalization of
`HarmonicBalls/LPStage/GFF.lean`. Imports: `CameronMartinDerived` only.
-/

namespace LatticeProb.Gauss

universe u

section CMBase

open MeasureTheory ProbabilityTheory Metric Set Laplacian
open scoped ENNReal ContDiff


/-- The test function `q_f = -(2π)⁻¹ Δ f` (Euclidean Laplacian), with `Δ` Mathlib's `Laplacian.laplacian`. -/
noncomputable def cmTestFn (f : ℂ → ℝ) (y : ℂ) : ℝ :=
  -(2 * Real.pi)⁻¹ * Δ f y

theorem contDiff_laplacian_of_contDiff' {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (Δ f) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_complexPlane]
  have hT : ContDiff ℝ (⊤ : ℕ∞) (iteratedFDeriv ℝ 2 f) := hf.iteratedFDeriv_right (by simp)
  have h1 : ∀ v : Fin 2 → ℂ, ContDiff ℝ (⊤ : ℕ∞) (fun x => iteratedFDeriv ℝ 2 f x v) := fun v =>
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => ℂ) ℝ v).contDiff.comp hT
  exact (h1 _).add (h1 _)

theorem cmTestFn_contDiff {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (cmTestFn f) :=
  contDiff_const.mul (contDiff_laplacian_of_contDiff' hf)

theorem cmTestFn_hasCompactSupport {f : ℂ → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (cmTestFn f) :=
  (hasCompactSupport_laplacian hc).mul_left

theorem cmTestFn_isTestFunction {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    IsTestFunction univ (cmTestFn f) :=
  ⟨cmTestFn_contDiff hf, cmTestFn_hasCompactSupport hc, subset_univ _⟩

/-- Logarithmic potential of `q_f`: `∫ log‖x - y‖ q_f(y) dy = -f(x)` (Newton kernel identity). -/
theorem integral_log_norm_mul_cmTestFn {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : ℂ) : ∫ y, Real.log ‖x - y‖ * cmTestFn f y = -f x := by
  have h := integral_newtonKernel_mul_laplacian (hf.of_le (by norm_num)) hc x
  rw [← h]
  congr 1
  ext y
  simp only [cmTestFn, newtonKernel]
  ring



/-- The truncated logarithm profile `w ↦ |log ‖w‖|` on `closedBall 0 (R+1)`, zero outside. -/
noncomputable def logDomProfile (R : ℝ) (w : ℂ) : ℝ :=
  (closedBall (0 : ℂ) (R + 1)).indicator (fun w => ‖Real.log ‖w‖‖) w

theorem integrable_logDomProfile (R : ℝ) : Integrable (logDomProfile R) := by
  have h0 : IntegrableOn (fun w : ℂ => ‖Real.log ‖w‖‖) (ball (0 : ℂ) (R + 2)) :=
    (integrableOn_ball_log_norm (R + 2)).norm
  have h1 : IntegrableOn (fun w : ℂ => ‖Real.log ‖w‖‖) (closedBall (0 : ℂ) (R + 1)) :=
    h0.mono_set (closedBall_subset_ball (by linarith))
  exact h1.integrable_indicator measurableSet_closedBall

theorem logDomProfile_nonneg (R : ℝ) (w : ℂ) : 0 ≤ logDomProfile R w := by
  unfold logDomProfile
  exact Set.indicator_nonneg (fun _ _ => norm_nonneg _) w

/-- Pointwise domination of the logarithmic kernel against a bounded test function supported in `closedBall 0 R`,
uniformly over the unit circle `‖c‖ = 1`. -/
theorem norm_log_mul_le_logDomProfile {q : ℂ → ℝ} {M R : ℝ} (hM : 0 ≤ M) (hqM : ∀ y, ‖q y‖ ≤ M)
    (hqR : ∀ y, R < ‖y‖ → q y = 0) {c : ℂ} (hc : ‖c‖ = 1) (y : ℂ) :
    ‖Real.log ‖c - y‖ * q y‖ ≤ M * logDomProfile R (c - y) := by
  by_cases h : ‖c - y‖ ≤ R + 1
  · have hmem : c - y ∈ closedBall (0 : ℂ) (R + 1) := by
      rw [mem_closedBall_zero_iff]; exact h
    have hΦ : logDomProfile R (c - y) = ‖Real.log ‖c - y‖‖ := by
      unfold logDomProfile; exact Set.indicator_of_mem hmem _
    rw [hΦ, norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hqM y) (norm_nonneg _)
  · have hy : R < ‖y‖ := by
      have : ‖c - y‖ ≤ ‖c‖ + ‖y‖ := norm_sub_le _ _
      linarith [not_le.mp h]
    rw [hqR y hy, mul_zero, norm_zero]
    exact mul_nonneg hM (logDomProfile_nonneg R _)


/-- Circle average over the unit circle, unfolded to the interval integral of `f (circleMap 0 1 θ)`. -/
theorem realCircleAverage_zero_one (g : ℂ → ℝ) :
    Real.circleAverage g 0 1 = (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, g (circleMap 0 1 θ) := by
  rw [Real.circleAverage_def, smul_eq_mul]

/-- The circle average of `log‖· - y‖` over the unit circle is `log⁺‖y‖` (Jensen, Mathlib). -/
theorem posLog_eq_circleAverage_log (y : ℂ) :
    Real.posLog ‖y‖ = (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, Real.log ‖circleMap 0 1 θ - y‖ := by
  rw [← realCircleAverage_zero_one (fun z => Real.log ‖z - y‖), circleAverage_log_norm_sub_const_eq_posLog]

/-- **Logarithmic potential of the Gaussian test function.** `∫ log⁺‖y‖ q_f(y) dy = -Av_{∂B_1(0)} f`, obtained by
writing `log⁺‖y‖` as the circle average of `log‖· - y‖` and exchanging the order of integration. -/
theorem integral_posLog_mul_cmTestFn {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∫ y, Real.posLog ‖y‖ * cmTestFn f y = -Real.circleAverage f 0 1 := by
  have hq_cont : Continuous (cmTestFn f) := (cmTestFn_contDiff hf).continuous
  have hq_cs : HasCompactSupport (cmTestFn f) := cmTestFn_hasCompactSupport hc
  obtain ⟨M, hM⟩ := hq_cont.bounded_above_of_compact_support hq_cs
  obtain ⟨R, hR⟩ := hq_cs.isCompact.isBounded.subset_closedBall 0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hqR : ∀ y, R < ‖y‖ → cmTestFn f y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have := hR h
    rw [mem_closedBall_zero_iff] at this
    linarith
  set G : ℝ → ℂ → ℝ := fun θ y => Real.log ‖circleMap 0 1 θ - y‖ * cmTestFn f y with hGdef
  have hnorm1 : ∀ θ : ℝ, ‖circleMap (0 : ℂ) 1 θ‖ = 1 := fun θ => by simp [norm_circleMap_zero]
  have hdom : ∀ θ : ℝ, ∀ y, ‖G θ y‖ ≤ M * logDomProfile R (circleMap 0 1 θ - y) :=
    fun θ y => norm_log_mul_le_logDomProfile hM0 hM hqR (hnorm1 θ) y
  have hGmeas : Measurable (fun p : ℝ × ℂ => G p.1 p.2) := by
    apply Measurable.mul
    · apply Real.measurable_log.comp
      apply continuous_norm.measurable.comp
      apply Measurable.sub
      · exact (continuous_circleMap 0 1).measurable.comp measurable_fst
      · exact measurable_snd
    · exact hq_cont.measurable.comp measurable_snd
  have hG1 : ∀ θ : ℝ, Integrable (G θ) := by
    intro θ
    refine Integrable.mono' (((integrable_logDomProfile R).comp_sub_left (circleMap 0 1 θ)).const_mul M) ?_
      (ae_of_all _ (hdom θ))
    exact (hGmeas.comp measurable_prodMk_left).aestronglyMeasurable
  have hI2 : Integrable (fun θ : ℝ => ∫ y, ‖G θ y‖) (volume.restrict (Ioc 0 (2 * Real.pi))) := by
    have hmeasI : AEStronglyMeasurable (fun θ : ℝ => ∫ y, ‖G θ y‖) (volume.restrict (Ioc 0 (2 * Real.pi))) :=
      (hGmeas.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    refine Integrable.mono' (integrable_const (M * ∫ w, logDomProfile R w)) hmeasI ?_
    refine ae_of_all _ (fun θ => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg (fun y => norm_nonneg _))]
    calc ∫ y, ‖G θ y‖ ≤ ∫ y, M * logDomProfile R (circleMap 0 1 θ - y) :=
          integral_mono (hG1 θ).norm (((integrable_logDomProfile R).comp_sub_left _).const_mul M)
            (fun y => hdom θ y)
      _ = M * ∫ w, logDomProfile R w := by
          rw [integral_const_mul, integral_sub_left_eq_self]
  have hH3 : Integrable (fun p : ℝ × ℂ => G p.1 p.2) ((volume.restrict (Ioc 0 (2 * Real.pi))).prod volume) :=
    (integrable_prod_iff hGmeas.aestronglyMeasurable).2 ⟨ae_of_all _ (fun θ => hG1 θ), hI2⟩
  have hH4 : Integrable (fun p : ℂ × ℝ => G p.2 p.1) (volume.prod (volume.restrict (Ioc 0 (2 * Real.pi)))) :=
    hH3.swap
  have hswap : ∫ y, ∫ θ in Ioc 0 (2 * Real.pi), G θ y = ∫ θ in Ioc 0 (2 * Real.pi), ∫ y, G θ y :=
    integral_integral_swap hH4
  have hint : ∀ y : ℂ, ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), G θ y =
      (∫ θ in (0 : ℝ)..2 * Real.pi, Real.log ‖circleMap 0 1 θ - y‖) * cmTestFn f y := by
    intro y
    rw [← intervalIntegral.integral_of_le (by positivity), ← intervalIntegral.integral_mul_const]
  have hstep1 : ∀ y : ℂ, Real.posLog ‖y‖ * cmTestFn f y =
      (2 * Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), G θ y := by
    intro y
    rw [hint y, posLog_eq_circleAverage_log y]
    ring
  have hstep3 : ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ∫ y, G θ y =
      ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), -f (circleMap 0 1 θ) := by
    refine integral_congr_ae (ae_of_all _ (fun θ => ?_))
    exact integral_log_norm_mul_cmTestFn hf hc (circleMap 0 1 θ)
  calc ∫ y, Real.posLog ‖y‖ * cmTestFn f y
      = (2 * Real.pi)⁻¹ * ∫ y, ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), G θ y := by
        simp_rw [hstep1]
        rw [integral_const_mul]
    _ = (2 * Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), ∫ y, G θ y := by rw [hswap]
    _ = (2 * Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), -f (circleMap 0 1 θ) := by rw [hstep3]
    _ = -Real.circleAverage f 0 1 := by
        rw [integral_neg, realCircleAverage_zero_one, ← intervalIntegral.integral_of_le (by positivity)]
        ring


/-- Pointwise domination of `log‖c - y‖ q(y)` for `‖c‖ ≤ K`, against the profile with radius `R + K`. -/
theorem norm_log_mul_le_logDomProfile' {q : ℂ → ℝ} {M R K : ℝ} (hM : 0 ≤ M) (hqM : ∀ y, ‖q y‖ ≤ M)
    (hqR : ∀ y, R < ‖y‖ → q y = 0) {c : ℂ} (hc : ‖c‖ ≤ K) (y : ℂ) :
    ‖Real.log ‖c - y‖ * q y‖ ≤ M * logDomProfile (R + K) (c - y) := by
  by_cases h : ‖c - y‖ ≤ R + K + 1
  · have hmem : c - y ∈ closedBall (0 : ℂ) (R + K + 1) := by
      rw [mem_closedBall_zero_iff]; exact h
    have hΦ : logDomProfile (R + K) (c - y) = ‖Real.log ‖c - y‖‖ := by
      unfold logDomProfile; exact Set.indicator_of_mem hmem _
    rw [hΦ, norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hqM y) (norm_nonneg _)
  · have hy : R < ‖y‖ := by
      have : ‖c - y‖ ≤ ‖c‖ + ‖y‖ := norm_sub_le _ _
      linarith [not_le.mp h]
    rw [hqR y hy, mul_zero, norm_zero]
    exact mul_nonneg hM (logDomProfile_nonneg _ _)

/-- Integrability of `y ↦ log‖c - y‖ q(y)` for a bounded measurable `q` supported in `closedBall 0 R`. -/
theorem integrable_log_sub_mul {q : ℂ → ℝ} {M R : ℝ} (hq : Measurable q) (hM : 0 ≤ M)
    (hqM : ∀ y, ‖q y‖ ≤ M) (hqR : ∀ y, R < ‖y‖ → q y = 0) (c : ℂ) :
    Integrable (fun y => Real.log ‖c - y‖ * q y) := by
  refine Integrable.mono' (((integrable_logDomProfile (R + ‖c‖)).comp_sub_left c).const_mul M) ?_
    (ae_of_all _ (fun y => norm_log_mul_le_logDomProfile' hM hqM hqR (le_refl ‖c‖) y))
  exact ((Real.measurable_log.comp (continuous_norm.measurable.comp (measurable_const.sub measurable_id))).mul
    hq).aestronglyMeasurable

/-- The logarithm of the Euclidean norm is the positive part of `log`: `log (max ‖z‖ 1) = log⁺ ‖z‖`. -/
theorem log_max_one_eq_posLog {r : ℝ} (hr : 0 ≤ r) : Real.log (max r 1) = Real.posLog r := by
  unfold Real.posLog
  rcases le_total r 1 with h | h
  · rw [max_eq_right h, Real.log_one, max_eq_left (Real.log_nonpos hr h)]
  · rw [max_eq_left h, max_eq_right (Real.log_nonneg h)]

/-- Off the diagonal the covariance kernel splits: `wholePlaneCov x y = log⁺‖x‖ + log⁺‖y‖ - log‖x - y‖`. -/
theorem wholePlaneCov_eq_of_ne {x y : ℂ} (h : y ≠ x) :
    wholePlaneCov x y = Real.posLog ‖x‖ + Real.posLog ‖y‖ - Real.log ‖x - y‖ := by
  unfold wholePlaneCov
  have hx : 0 < max ‖x‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hy : 0 < max ‖y‖ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hxy : ‖x - y‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]; exact fun h' => h h'.symm
  rw [Real.log_div (mul_pos hx hy).ne' hxy, Real.log_mul hx.ne' hy.ne', log_max_one_eq_posLog (norm_nonneg _),
    log_max_one_eq_posLog (norm_nonneg _)]


/-- Uniform bounds for `q_f`: bounded by `M`, vanishing outside `closedBall 0 R`. -/
theorem cmTestFn_bounds {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ M R : ℝ, 0 ≤ M ∧ (∀ y, ‖cmTestFn f y‖ ≤ M) ∧ (∀ y, R < ‖y‖ → cmTestFn f y = 0) := by
  have hq_cs : HasCompactSupport (cmTestFn f) := cmTestFn_hasCompactSupport hc
  obtain ⟨M, hM⟩ := (cmTestFn_contDiff hf).continuous.bounded_above_of_compact_support hq_cs
  obtain ⟨R, hR⟩ := hq_cs.isCompact.isBounded.subset_closedBall 0
  refine ⟨M, R, (norm_nonneg _).trans (hM 0), hM, fun y hy => ?_⟩
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have := hR h
  rw [mem_closedBall_zero_iff] at this
  linarith

/-- **The covariance identity (1).** For `Av_{∂B_1(0)} f = 0`-free data: `∫ K(x,y) q_f(y) dy = f(x) - Av_{∂B_1} f`
for every `x`, where `K = wholePlaneCov` is the whole-plane GFF covariance kernel (eq:cov-kernel). -/
theorem integral_wholePlaneCov_mul_cmTestFn {f : ℂ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (x : ℂ) : ∫ y, wholePlaneCov x y * cmTestFn f y = f x - Real.circleAverage f 0 1 := by
  obtain ⟨M, R, hM0, hqM, hqR⟩ := cmTestFn_bounds hf hc
  have hq_cont : Continuous (cmTestFn f) := (cmTestFn_contDiff hf).continuous
  have hq_int : Integrable (cmTestFn f) :=
    hq_cont.integrable_of_hasCompactSupport (cmTestFn_hasCompactSupport hc)
  have hq0 : ∫ y, cmTestFn f y = 0 := by
    unfold cmTestFn
    rw [integral_const_mul, integral_laplacian_eq_zero (hf.of_le (by norm_num)) hc, mul_zero]
  have hpos_int : Integrable (fun y => Real.posLog ‖y‖ * cmTestFn f y) :=
    ((Real.continuous_posLog.comp continuous_norm).mul hq_cont).integrable_of_hasCompactSupport
      (cmTestFn_hasCompactSupport hc).mul_left
  have hlog_int : Integrable (fun y => Real.log ‖x - y‖ * cmTestFn f y) :=
    integrable_log_sub_mul hq_cont.measurable hM0 hqM hqR x
  have hconst_int : Integrable (fun y => Real.posLog ‖x‖ * cmTestFn f y) := hq_int.const_mul _
  calc ∫ y, wholePlaneCov x y * cmTestFn f y
      = ∫ y, (Real.posLog ‖x‖ * cmTestFn f y + Real.posLog ‖y‖ * cmTestFn f y
          - Real.log ‖x - y‖ * cmTestFn f y) := by
        refine integral_congr_ae ?_
        filter_upwards [ae_ne_complex x] with y hy
        rw [wholePlaneCov_eq_of_ne hy]
        ring
    _ = (∫ y, Real.posLog ‖x‖ * cmTestFn f y) + (∫ y, Real.posLog ‖y‖ * cmTestFn f y)
          - ∫ y, Real.log ‖x - y‖ * cmTestFn f y := by
        have hsum : Integrable (fun y => Real.posLog ‖x‖ * cmTestFn f y + Real.posLog ‖y‖ * cmTestFn f y) :=
          hconst_int.add hpos_int
        rw [integral_sub hsum hlog_int, integral_add hconst_int hpos_int]
    _ = f x - Real.circleAverage f 0 1 := by
        rw [integral_const_mul, hq0, integral_posLog_mul_cmTestFn hf hc,
          integral_log_norm_mul_cmTestFn hf hc x]
        ring


/-! ### Gaussian tilt of a centered Gaussian pair -/

section Tilt

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- A centered Gaussian real variable of zero variance vanishes almost surely. -/
theorem ae_eq_zero_of_variance_eq_zero {X : Ω → ℝ} (hX : HasGaussianLaw X P) (hX0 : P[X] = 0)
    (hv : Var[X; P] = 0) : ∀ᵐ x ∂P, X x = 0 := by
  have hlaw := hX.map_eq_gaussianReal
  rw [hX0, hv, Real.toNNReal_zero, gaussianReal_zero_var] at hlaw
  have h1 : ∀ᵐ x ∂(P.map X), x = 0 := by
    rw [hlaw]
    exact (ae_dirac_iff (measurableSet_singleton (0 : ℝ))).2 rfl
  exact (ae_map_iff hX.aemeasurable (measurableSet_singleton (0 : ℝ))).1 h1

omit [IsProbabilityMeasure P] in
/-- A covariance with a variable which vanishes almost surely is zero. -/
theorem covariance_eq_zero_of_ae_eq_zero {W X : Ω → ℝ} (hX : ∀ᵐ x ∂P, X x = 0) : cov[W, X; P] = 0 := by
  have hX0 : P[X] = 0 := by
    rw [integral_congr_ae (g := fun _ => (0 : ℝ)) hX]
    simp
  unfold covariance
  have h0 : (fun x => (W x - P[W]) * (X x - P[X])) =ᵐ[P] fun _ => (0 : ℝ) := by
    filter_upwards [hX] with x hx
    simp [hx, hX0]
  rw [integral_congr_ae h0]
  simp

/-- **Gaussian tilt, one-dimensional core.** For a centered Gaussian pair `(X, W)` with `Var X = v` and
`Cov(W, X) = c`, the tilt `exp(-X - v/2)` gives `E[exp(-X - v/2) exp(i W)] = exp(-i c - Var W / 2)`. -/
theorem tilt_core {X W : Ω → ℝ} (hXW : HasGaussianLaw (fun x => (X x, W x)) P) (hX0 : P[X] = 0)
    (hW0 : P[W] = 0) :
    ∫ x, ((Real.exp (-X x - Var[X; P] / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (W x : ℂ)) ∂P
      = Complex.exp (-(Complex.I * (cov[W, X; P] : ℂ)) - ((Var[W; P] : ℝ) : ℂ) / 2) := by
  have hX : HasGaussianLaw X P := hXW.map (ContinuousLinearMap.fst ℝ ℝ ℝ)
  have hW : HasGaussianLaw W P := hXW.map (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hXm : MemLp X 2 P := hX.memLp_two
  have hWm : MemLp W 2 P := hW.memLp_two
  obtain ⟨β, hβv⟩ : ∃ β : ℝ, β * Var[X; P] = cov[W, X; P] := by
    by_cases hv : Var[X; P] = 0
    · exact ⟨0, by rw [zero_mul]; exact (covariance_eq_zero_of_ae_eq_zero
        (ae_eq_zero_of_variance_eq_zero hX hX0 hv)).symm⟩
    · exact ⟨cov[W, X; P] / Var[X; P], div_mul_cancel₀ _ hv⟩
  -- the residual W' = W - β X
  have hjoint : HasGaussianLaw (fun x => (X x, (W - β • X) x)) P :=
    hXW.map ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      ((ContinuousLinearMap.snd ℝ ℝ ℝ) - β • ContinuousLinearMap.fst ℝ ℝ ℝ))
  have hW'G : HasGaussianLaw (W - β • X) P := hjoint.map (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hW'm : MemLp (W - β • X) 2 P := hW'G.memLp_two
  have hcov : cov[X, (W - β • X); P] = 0 := by
    rw [covariance_comm, covariance_sub_left hWm (hXm.const_smul β) hXm, covariance_smul_left,
      covariance_self hX.aemeasurable, hβv, sub_self]
  have hind : IndepFun X (W - β • X) P := HasGaussianLaw.indepFun_of_covariance_eq_zero hjoint hcov
  -- Laws of X and of the residual
  have hXint : Integrable X P := hXm.integrable one_le_two
  have hWint : Integrable W P := hWm.integrable one_le_two
  have hlawX : HasLaw X (gaussianReal 0 (Var[X; P]).toNNReal) P := by
    refine ⟨hX.aemeasurable, ?_⟩
    have h := hX.map_eq_gaussianReal
    rwa [hX0] at h
  have hW'0 : P[W - β • X] = 0 := by
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_sub hWint (hXint.const_mul β), integral_const_mul, hW0, hX0, mul_zero, sub_zero]
  have hW'law : HasLaw (W - β • X) (gaussianReal 0 (Var[W - β • X; P]).toNNReal) P := by
    refine ⟨hW'G.aemeasurable, ?_⟩
    have h := hW'G.map_eq_gaussianReal
    rwa [hW'0] at h
  -- Variance decomposition Var W = Var W' + β² Var X
  have hβX : MemLp (β • X) 2 P := hXm.const_smul β
  have hVar : Var[W; P] = Var[W - β • X; P] + β ^ 2 * Var[X; P] := by
    have e : W = (W - β • X) + β • X := by funext x; simp
    have h1 := variance_add hW'm hβX
    rw [← e] at h1
    have hc0 : cov[W - β • X, X; P] = 0 := by rw [covariance_comm]; exact hcov
    rw [h1, covariance_smul_right, hc0, variance_smul]
    ring
  -- Characteristic functions of the two independent pieces
  have hv0 : 0 ≤ Var[X; P] := variance_nonneg _ _
  have hf_eval : ∫ x, Complex.exp ((-1 + Complex.I * β) * (X x : ℂ)) ∂P
      = Complex.exp (((Var[X; P] : ℝ) : ℂ) * (-1 + Complex.I * β) ^ 2 / 2) := by
    have h := complexMGF_gaussianReal hlawX (-1 + Complex.I * β)
    unfold complexMGF at h
    rw [h]
    congr 1
    simp [Real.coe_toNNReal _ hv0]
  have hg_eval : ∫ x, Complex.exp (Complex.I * ((W - β • X) x : ℂ)) ∂P
      = Complex.exp (-((Var[W - β • X; P] : ℝ) : ℂ) / 2) := by
    have h1 : ∫ x, Complex.exp (Complex.I * ((W - β • X) x : ℂ)) ∂P = charFun (P.map (W - β • X)) 1 := by
      rw [charFun_apply_real, integral_map hW'G.aemeasurable (by fun_prop)]
      apply integral_congr_ae
      filter_upwards with x
      push_cast
      ring_nf
    rw [h1, hW'law.map_eq, charFun_gaussianReal]
    congr 1
    simp [Real.coe_toNNReal _ (variance_nonneg _ _)]
    ring
  -- Pointwise factorisation of the tilted integrand
  have hpt : ∀ x : Ω, ((Real.exp (-X x - Var[X; P] / 2) : ℝ) : ℂ) * Complex.exp (Complex.I * (W x : ℂ))
      = Complex.exp (-((Var[X; P] : ℝ) : ℂ) / 2)
        * (Complex.exp ((-1 + Complex.I * β) * (X x : ℂ)) * Complex.exp (Complex.I * ((W - β • X) x : ℂ))) := by
    intro x
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_const_mul]
  have hprod := hind.integral_comp_mul_comp
    (f := fun x : ℝ => Complex.exp ((-1 + Complex.I * β) * (x : ℂ)))
    (g := fun x : ℝ => Complex.exp (Complex.I * (x : ℂ)))
    hX.aemeasurable hW'G.aemeasurable (by fun_prop) (by fun_prop)
  have hprod' : ∫ x, Complex.exp ((-1 + Complex.I * β) * (X x : ℂ)) * Complex.exp (Complex.I * ((W - β • X) x : ℂ)) ∂P
      = (∫ x, Complex.exp ((-1 + Complex.I * β) * (X x : ℂ)) ∂P)
        * ∫ x, Complex.exp (Complex.I * ((W - β • X) x : ℂ)) ∂P := hprod
  rw [hprod', hf_eval, hg_eval, ← Complex.exp_add, ← Complex.exp_add, ← hβv]
  congr 1
  rw [hVar]
  push_cast
  linear_combination (↑β ^ 2 * ↑(Var[X; P]) / 2 : ℂ) * Complex.I_sq

end Tilt

end CMBase

section CMDerived

open MeasureTheory ProbabilityTheory Metric Set Laplacian
open scoped ENNReal ContDiff

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem clm_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (z : ι → ℝ) :
    L z = ∑ i, z i * L (fun j => if i = j then 1 else 0) := by
  conv_lhs => rw [pi_eq_sum_univ z]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, smul_eq_mul]

/-- The shifted family and the tilt: for every continuous linear functional `L` on the coordinates of a finite
family `I`, the characteristic functional of the tilted shifted family equals that of the original family. -/
theorem law_shift_charFun {T : Type*} {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hYm : ∀ t, Measurable (Y t)) (hcen : ∀ t, P[Y t] = 0) (q : T) (a : T → ℝ)
    (hcov : ∀ t, cov[Y t, Y q; P] = a t) (I : Finset T) (L : StrongDual ℝ (I → ℝ)) :
    ∫ x, Complex.exp (L (fun t : I => Y t x + a t) * Complex.I)
        ∂(P.withDensity (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2))))
      = ∫ x, Complex.exp (L (fun t : I => Y t x) * Complex.I) ∂P := by
  classical
  have hXG : HasGaussianLaw (Y q) P := hY.hasGaussianLaw_eval q
  have hXm : MemLp (Y q) 2 P := hXG.memLp_two
  have hv0 : 0 ≤ Var[Y q; P] := variance_nonneg _ _
  -- Gaussian family on J = insert q I, and the two linear functionals
  set J : Finset T := insert q I with hJ
  have hZJ : HasGaussianLaw (fun x (t : J) => Y t x) P := hY.hasGaussianLaw J
  have hqJ : q ∈ J := Finset.mem_insert_self q I
  let ℓ₁ : (J → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj ⟨q, hqJ⟩
  let R : (J → ℝ) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi (fun t : I => ContinuousLinearMap.proj ⟨(t : T), Finset.mem_insert_of_mem t.2⟩)
  let ℓ₂ : (J → ℝ) →L[ℝ] ℝ := L.comp R
  have hpair : HasGaussianLaw (fun x => (Y q x, L (fun t : I => Y t x))) P := hZJ.map (ℓ₁.prod ℓ₂)
  have hW : HasGaussianLaw (fun x => L (fun t : I => Y t x)) P := hpair.map (ContinuousLinearMap.snd ℝ ℝ ℝ)
  -- coefficients of the functional
  set c : I → ℝ := fun i => L (fun j => if i = j then 1 else 0) with hc_def
  have hαsum : L (fun t : I => a t) = ∑ i : I, c i * a i := by
    rw [clm_apply_eq_sum L]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hWsum : (fun x => L (fun t : I => Y t x)) = ∑ i : I, c i • Y i := by
    funext x
    rw [clm_apply_eq_sum L, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have hMem : ∀ i : I, MemLp (Y i) 2 P := fun i => (hY.hasGaussianLaw_eval (i : T)).memLp_two
  have hW0 : P[fun x => L (fun t : I => Y t x)] = 0 := by
    rw [hWsum]
    show ∫ x, (∑ i : I, c i • Y i) x ∂P = 0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ (fun i _ => ((hMem i).integrable one_le_two).const_mul (c i))]
    simp [integral_const_mul, hcen]
  have hcovWX : cov[fun x => L (fun t : I => Y t x), Y q; P] = L (fun t : I => a t) := by
    rw [hWsum, covariance_sum_left (X := fun i : I => c i • Y i) (fun i => (hMem i).const_smul (c i)) hXm]
    simp only [covariance_smul_left, hcov]
    rw [hαsum]
  have hXlaw : HasLaw (Y q) (gaussianReal 0 (Var[Y q; P]).toNNReal) P := by
    refine ⟨(hYm q).aemeasurable, ?_⟩
    have h := (hXG).map_eq_gaussianReal
    rwa [hcen q] at h
  have hWlaw : HasLaw (fun x => L (fun t : I => Y t x))
      (gaussianReal 0 (Var[fun x => L (fun t : I => Y t x); P]).toNNReal) P := by
    refine ⟨hW.aemeasurable, ?_⟩
    have h := hW.map_eq_gaussianReal
    rwa [hW0] at h
  have hDmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hYm q).neg.sub_const _))
  rw [integral_withDensity_eq_integral_toReal_smul₀ hDmeas.aemeasurable
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  have hlhs : ∀ x : Ω, (ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2))).toReal
      • Complex.exp (L (fun t : I => Y t x + a t) * Complex.I)
      = Complex.exp (L (fun t : I => a t) * Complex.I)
        * (((Real.exp (-Y q x - Var[Y q; P] / 2) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((L (fun t : I => Y t x) : ℝ) : ℂ))) := by
    intro x
    have e : (fun t : I => Y t x + a t) = (fun t : I => Y t x) + (fun t : I => a t) := rfl
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, e, map_add, Complex.ofReal_add,
      add_mul, Complex.exp_add, mul_comm (((L (fun t : I => Y t x)) : ℝ) : ℂ) Complex.I, Complex.ofReal_exp]
    ring
  rw [integral_congr_ae (ae_of_all _ hlhs), integral_const_mul]
  rw [tilt_core hpair (hcen q) hW0, hcovWX]
  have hR : ∫ x, Complex.exp (L (fun t : I => Y t x) * Complex.I) ∂P
      = Complex.exp (-((Var[fun x => L (fun t : I => Y t x); P] : ℝ) : ℂ) / 2) := by
    have h1 : ∫ x, Complex.exp (L (fun t : I => Y t x) * Complex.I) ∂P
        = charFun (P.map (fun x => L (fun t : I => Y t x))) 1 := by
      rw [charFun_apply_real, integral_map hW.aemeasurable (by fun_prop)]
      apply integral_congr_ae
      filter_upwards with x
      push_cast
      ring_nf
    rw [h1, hWlaw.map_eq, charFun_gaussianReal]
    congr 1
    simp [Real.coe_toNNReal _ (variance_nonneg _ _)]
    ring
  rw [hR, ← Complex.exp_add]
  congr 1
  ring

/-- **Shift of the finite-dimensional law (Cameron-Martin tilt).** Under the tilt `dP'/dP = exp(-X - v/2)`, `X = Y q`,
the family `Y + a` (with `a t = Cov(Y t, X)`) has the same finite-dimensional law as `Y` under `P`. -/
theorem law_shift {T : Type*} {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hYm : ∀ t, Measurable (Y t)) (hcen : ∀ t, P[Y t] = 0) (q : T) (a : T → ℝ)
    (hcov : ∀ t, cov[Y t, Y q; P] = a t) (I : Finset T) :
    (P.withDensity (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2)))).map
        (fun x (t : I) => Y t x + a t)
      = P.map (fun x (t : I) => Y t x) := by
  have hint : Integrable (fun x => Real.exp (-Y q x)) P := by
    have hXlaw : HasLaw (Y q) (gaussianReal 0 (Var[Y q; P]).toNNReal) P := by
      refine ⟨(hYm q).aemeasurable, ?_⟩
      have h := (hY.hasGaussianLaw_eval q).map_eq_gaussianReal
      rwa [hcen q] at h
    have h1 : Integrable (fun y : ℝ => Real.exp (-1 * y)) (gaussianReal 0 (Var[Y q; P]).toNNReal) :=
      integrable_exp_mul_gaussianReal (-1)
    have h2 : Integrable (fun y : ℝ => Real.exp (-y)) (gaussianReal 0 (Var[Y q; P]).toNNReal) := by
      simpa using h1
    have h3 : Integrable (fun y : ℝ => Real.exp (-y)) (P.map (Y q)) := by
      rw [hXlaw.map_eq]; exact h2
    exact (integrable_map_measure (Real.measurable_exp.comp measurable_neg).aestronglyMeasurable
      (hYm q).aemeasurable).1 h3
  have hDint : Integrable (fun x => Real.exp (-Y q x - Var[Y q; P] / 2)) P := by
    have e : (fun x => Real.exp (-Y q x - Var[Y q; P] / 2))
        = fun x => Real.exp (-Y q x) * Real.exp (-(Var[Y q; P] / 2)) := by
      funext x
      rw [← Real.exp_add]
      ring_nf
    rw [e]
    exact hint.mul_const _
  have : IsFiniteMeasure (P.withDensity (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2)))) :=
    isFiniteMeasure_withDensity_ofReal hDint.hasFiniteIntegral
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply, charFunDual_apply]
  have hZ' : Measurable (fun x (t : I) => Y t x + a t) :=
    Measurable.of_eval (fun t => (hYm t).add_const _)
  have hZ : Measurable (fun x (t : I) => Y t x) := Measurable.of_eval (fun t => hYm t)
  have hcont : Continuous (fun z : I → ℝ => Complex.exp (L z * Complex.I)) := by fun_prop
  rw [integral_map hZ'.aemeasurable hcont.aestronglyMeasurable,
    integral_map hZ.aemeasurable hcont.aestronglyMeasurable]
  exact law_shift_charFun hY hYm hcen q a hcov I L

end Law


/-! ### Assembly helpers -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Evaluation of a shifted observable: the pairing is shifted by `∫ f φ`, the circle average by `Av f`. -/
theorem eval_addFunPairing (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (f : ℂ → ℝ) (o : GFFObservable) :
    o.eval (addFunPairing hC f) (fun r z => hcirc r z + Real.circleAverage f z r)
      = o.eval hC hcirc + o.smear f := by
  cases o with
  | pairing φ =>
    simp only [GFFObservable.eval, GFFObservable.smear, addFunPairing]
    congr 1
    refine integral_congr_ae (ae_of_all _ (fun x => ?_))
    ring
  | circle r z => simp [GFFObservable.eval, GFFObservable.smear]

omit [MeasurableSpace Ω] in
/-- The circle average `(r, z) ↦ Av_{∂B_r(z)} f` is continuous for continuous `f`. -/
theorem continuous_realCircleAverage {f : ℂ → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1) := by
  have h : Continuous fun p : ℝ × ℂ => ∫ t in (0 : ℝ)..2 * Real.pi, f (circleMap p.2 p.1 t) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (f := fun p : ℝ × ℂ => fun t : ℝ => f (circleMap p.2 p.1 t)) ?_ continuous_const
    refine hf.comp ?_
    have hc : Continuous fun q : (ℝ × ℂ) × ℝ => circleMap q.1.2 q.1.1 q.2 := by
      unfold circleMap
      fun_prop
    exact hc
  have e : (fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1)
      = fun p : ℝ × ℂ => (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi, f (circleMap p.2 p.1 t) := by
    funext p
    rw [Real.circleAverage_def, smul_eq_mul]
  rw [e]
  exact continuous_const.mul h

/-- Covariances are determined by the joint law of the two variables. -/
theorem cov_eq_of_map_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X Y : Ω → ℝ} {X' Y' : Ω' → ℝ}
    (hXY : μ.map (fun x => (X x, Y x)) = ν.map (fun x => (X' x, Y' x)))
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hX' : MemLp X' 2 ν) (hY' : MemLp Y' 2 ν) :
    cov[X, Y; μ] = cov[X', Y'; ν] := by
  have hpair : AEMeasurable (fun x => (X x, Y x)) μ :=
    hX.aestronglyMeasurable.aemeasurable.prodMk hY.aestronglyMeasurable.aemeasurable
  have hpair' : AEMeasurable (fun x => (X' x, Y' x)) ν :=
    hX'.aestronglyMeasurable.aemeasurable.prodMk hY'.aestronglyMeasurable.aemeasurable
  have hI : ∀ g : ℝ × ℝ → ℝ, Continuous g →
      ∫ x, g (X x, Y x) ∂μ = ∫ x, g (X' x, Y' x) ∂ν := by
    intro g hg
    rw [← integral_map hpair hg.aestronglyMeasurable, ← integral_map hpair' hg.aestronglyMeasurable, hXY]
  rw [covariance_eq_sub hX hY, covariance_eq_sub hX' hY']
  have e1 := hI (fun p => p.1 * p.2) (by fun_prop)
  have e2 := hI (fun p => p.1) continuous_fst
  have e3 := hI (fun p => p.2) continuous_snd
  simp only at e1 e2 e3
  simp only [Pi.mul_apply]
  rw [e1, e2, e3]

/-- The tilt `exp(-X - v/2)` of a centered Gaussian `X` with variance `v` is a probability density. -/
theorem isProbabilityMeasure_tilt {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 (Var[X; P]).toNNReal) P) (hv0 : 0 ≤ Var[X; P]) :
    IsProbabilityMeasure (P.withDensity (fun x => ENNReal.ofReal (Real.exp (-X x - Var[X; P] / 2)))) := by
  have hint : Integrable (fun x => Real.exp (-X x)) P := by
    have h1 : Integrable (fun y : ℝ => Real.exp (-1 * y)) (gaussianReal 0 (Var[X; P]).toNNReal) :=
      integrable_exp_mul_gaussianReal (-1)
    have h2 : Integrable (fun y : ℝ => Real.exp (-y)) (gaussianReal 0 (Var[X; P]).toNNReal) := by
      simpa using h1
    have h3 : Integrable (fun y : ℝ => Real.exp (-y)) (P.map X) := by
      rw [hX.map_eq]; exact h2
    exact (integrable_map_measure (Real.measurable_exp.comp measurable_neg).aestronglyMeasurable
      hX.aemeasurable).1 h3
  have hmgf : ∫ x, Real.exp (-X x) ∂P = Real.exp (Var[X; P] / 2) := by
    have h := mgf_gaussianReal hX (-1)
    unfold mgf at h
    simp only [neg_one_mul, zero_mul, zero_add, Real.coe_toNNReal _ hv0] at h
    rw [h]
    congr 1
    ring
  have e : (fun x => Real.exp (-X x - Var[X; P] / 2))
      = fun x => Real.exp (-X x) * Real.exp (-(Var[X; P] / 2)) := by
    funext x
    rw [← Real.exp_add]
    ring_nf
  have hmass : ∫ x, Real.exp (-X x - Var[X; P] / 2) ∂P = 1 := by
    rw [e, integral_mul_const, hmgf, ← Real.exp_add]
    simp
  have hDint : Integrable (fun x => Real.exp (-X x - Var[X; P] / 2)) P := by
    rw [e]
    exact hint.mul_const _
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hDint (ae_of_all _ (fun x => (Real.exp_pos _).le)), hmass]
  simp

end Assembly


/-! ### The derived Cameron-Martin reweighting -/

section Main

/-- **Cameron-Martin reweighting of the whole-plane GFF, derived.** For every whole-plane GFF `(P, hC, hcirc)` and
every smooth compactly supported `f` with zero unit-circle average, the measure `P' = exp(-X - Var X / 2) · P`, with
`X = hC(-(2π)⁻¹ Δ f)`, is equivalent to `P` and under `P'` the shifted pairings and circle averages form a whole-plane
GFF. This is the frozen input `CameronMartinGFFReweighting` (`FirstPass/Frozen/S11aj.lean:33`), exactly as typed. -/
theorem cameronMartinGFFReweighting_derived : CameronMartinGFFReweighting.{u} := by
  intro Ω _ P _ hC hcirc hGFF f hf hc hAv
  -- the observables as a Gaussian process indexed by the admissible observables
  let Y : GFFObservable.Admissible → Ω → ℝ := fun o x => o.1.eval (hC x) (hcirc x)
  have hYG : IsGaussianProcess Y P := hGFF.isGaussianProcess
  have hYm : ∀ o : GFFObservable.Admissible, Measurable (Y o) := by
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact hGFF.measurable_pairing φ ho
    | circle r z => exact hGFF.measurable_circle r z ho
  have hcen : ∀ o : GFFObservable.Admissible, P[Y o] = 0 := fun o => hGFF.integral_eq_zero o.1 o.2
  -- the Gaussian variable `X = hC(q_f)` and the shifts `a_o = o.smear f`
  let q : GFFObservable.Admissible := ⟨GFFObservable.pairing (cmTestFn f), cmTestFn_isTestFunction hf hc⟩
  let a : GFFObservable.Admissible → ℝ := fun o => o.1.smear f
  have hcov : ∀ o : GFFObservable.Admissible, cov[Y o, Y q; P] = a o := by
    intro o
    have hfun : (fun x => (GFFObservable.pairing (cmTestFn f)).smear (fun y => wholePlaneCov x y)) = f := by
      funext x
      have h2 := integral_wholePlaneCov_mul_cmTestFn hf hc x
      rw [hAv, sub_zero] at h2
      simp only [GFFObservable.smear]
      rw [← h2]
      exact integral_congr_ae (ae_of_all _ (fun y => mul_comm _ _))
    have h := hGFF.covariance_eq o.1 q.1 o.2 q.2
    refine h.trans ?_
    unfold wholePlaneGFFCov
    change o.1.smear (fun x => (GFFObservable.pairing (cmTestFn f)).smear (fun y => wholePlaneCov x y))
      = o.1.smear f
    rw [hfun]
  have hXlaw : HasLaw (Y q) (gaussianReal 0 (Var[Y q; P]).toNNReal) P := by
    refine ⟨(hYm q).aemeasurable, ?_⟩
    have h := (hYG.hasGaussianLaw_eval q).map_eq_gaussianReal
    rwa [hcen q] at h
  -- the tilted measure
  set P' := P.withDensity (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2))) with hP'
  have : IsProbabilityMeasure P' := isProbabilityMeasure_tilt hXlaw (variance_nonneg _ _)
  have hshift := law_shift hYG hYm hcen q a hcov
  have hevalEq : ∀ (x : Ω) (o : GFFObservable.Admissible),
      o.1.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r) = Y o x + a o := by
    intro x o
    rw [eval_addFunPairing]
  have hYG' : IsGaussianProcess (fun (o : GFFObservable.Admissible) (x : Ω) =>
      o.1.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r)) P' := by
    refine ⟨fun I => ?_⟩
    have hfun : (fun x => I.restrict (fun o : GFFObservable.Admissible =>
        o.1.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r)))
        = fun x (t : I) => Y t x + a t := by
      funext x t
      exact hevalEq x t
    rw [hfun]
    refine ⟨(Measurable.of_eval (fun t : I => (hYm t).add_const (a t))).aemeasurable, ?_⟩
    rw [hshift I]
    exact (hYG.hasGaussianLaw I).isGaussian_map
  have hDmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hYm q).neg.sub_const _))
  refine ⟨P', withDensity_absolutelyContinuous P _,
    withDensity_absolutelyContinuous' hDmeas.aemeasurable
      (ae_of_all _ (fun x => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')), ?_⟩
  refine
    { measurable_pairing := fun φ hφ => (hGFF.measurable_pairing φ hφ).add_const _
      measurable_circle := fun r z hr => (hGFF.measurable_circle r z hr).add_const _
      isGaussianProcess := hYG'
      integral_eq_zero := ?_
      covariance_eq := ?_
      ae_continuousOn_circle := ?_ }
  · -- the mean of each shifted observable is zero
    intro o ho
    let oa : GFFObservable.Admissible := ⟨o, ho⟩
    have hfun : (fun x => o.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r))
        = fun x => Y oa x + a oa := funext (fun x => hevalEq x oa)
    show ∫ x, o.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r) ∂P' = 0
    rw [hfun]
    have hs : (⟨oa, Finset.mem_singleton_self oa⟩ : ({oa} : Finset GFFObservable.Admissible)) = ⟨oa, Finset.mem_singleton_self oa⟩ := rfl
    have hmeasEv : Measurable (fun g : ({oa} : Finset GFFObservable.Admissible) → ℝ =>
        g ⟨oa, Finset.mem_singleton_self oa⟩) := measurable_pi_apply _
    have hZ1 : Measurable (fun x (t : ({oa} : Finset GFFObservable.Admissible)) => Y t x + a t) :=
      Measurable.of_eval (fun t => (hYm t).add_const (a t))
    have hZ0 : Measurable (fun x (t : ({oa} : Finset GFFObservable.Admissible)) => Y t x) :=
      Measurable.of_eval (fun t => hYm t)
    have h1 : P'.map (fun x => Y oa x + a oa) = P.map (Y oa) := by
      have h := congrArg (Measure.map (fun g : ({oa} : Finset GFFObservable.Admissible) → ℝ =>
        g ⟨oa, Finset.mem_singleton_self oa⟩)) (hshift {oa})
      rw [Measure.map_map hmeasEv hZ1, Measure.map_map hmeasEv hZ0] at h
      exact h
    have hmeas : Measurable (fun x => Y oa x + a oa) := (hYm oa).add_const _
    have hint : ∫ x, Y oa x + a oa ∂P' = ∫ y, y ∂(P'.map (fun x => Y oa x + a oa)) := by
      rw [integral_map (f := fun y : ℝ => y) hmeas.aemeasurable (by fun_prop)]
    rw [hint, h1, integral_map (f := fun y : ℝ => y) (hYm oa).aemeasurable (by fun_prop)]
    simpa using hcen oa
  · -- the covariances are those of the original process
    intro o o' ho ho'
    let oa : GFFObservable.Admissible := ⟨o, ho⟩
    let ob : GFFObservable.Admissible := ⟨o', ho'⟩
    have hfun1 : (fun x => o.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r))
        = fun x => Y oa x + a oa := funext (fun x => hevalEq x oa)
    have hfun2 : (fun x => o'.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r))
        = fun x => Y ob x + a ob := funext (fun x => hevalEq x ob)
    show cov[fun x => o.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r),
      fun x => o'.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r); P'] = _
    rw [hfun1, hfun2]
    classical
    have hmeasPair : Measurable (fun g : ({oa, ob} : Finset GFFObservable.Admissible) → ℝ =>
        (g ⟨oa, Finset.mem_insert_self _ _⟩, g ⟨ob, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    have hZ1 : Measurable (fun x (t : ({oa, ob} : Finset GFFObservable.Admissible)) => Y t x + a t) :=
      Measurable.of_eval (fun t => (hYm t).add_const (a t))
    have hZ0 : Measurable (fun x (t : ({oa, ob} : Finset GFFObservable.Admissible)) => Y t x) :=
      Measurable.of_eval (fun t => hYm t)
    have hJ : P'.map (fun x => (Y oa x + a oa, Y ob x + a ob)) = P.map (fun x => (Y oa x, Y ob x)) := by
      have h := congrArg (Measure.map (fun g : ({oa, ob} : Finset GFFObservable.Admissible) → ℝ =>
        (g ⟨oa, Finset.mem_insert_self _ _⟩, g ⟨ob, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)))
        (hshift {oa, ob})
      rw [Measure.map_map hmeasPair hZ1, Measure.map_map hmeasPair hZ0] at h
      exact h
    have hMX' : MemLp (fun x => Y oa x + a oa) 2 P' := by
      rw [← hfun1]; exact (hYG'.hasGaussianLaw_eval oa).memLp_two
    have hMY' : MemLp (fun x => Y ob x + a ob) 2 P' := by
      rw [← hfun2]; exact (hYG'.hasGaussianLaw_eval ob).memLp_two
    have hMX : MemLp (Y oa) 2 P := (hYG.hasGaussianLaw_eval oa).memLp_two
    have hMY : MemLp (Y ob) 2 P := (hYG.hasGaussianLaw_eval ob).memLp_two
    rw [cov_eq_of_map_eq hJ hMX' hMY' hMX hMY]
    exact hGFF.covariance_eq o o' ho ho'
  · -- continuity of the circle average process transfers along `P' ≪ P`
    have h0 := hGFF.ae_continuousOn_circle
    have h1 := (withDensity_absolutelyContinuous P (fun x => ENNReal.ofReal
      (Real.exp (-Y q x - Var[Y q; P] / 2)))).ae_le h0
    filter_upwards [h1] with x hx
    exact hx.add (continuous_realCircleAverage hf.continuous).continuousOn

end Main

end CMDerived

section CMMutualAbsCont

open MeasureTheory Set
open scoped ENNReal


open MeasureTheory Set
open scoped ENNReal


/-- The evaluation of a distribution on the test functions of `univ`, as a function on the index type
`LocalFieldTest univ`. -/
noncomputable def cmDerivedEval : ((ℂ → ℝ) → ℝ) → (LocalFieldTest Set.univ → ℝ) :=
  fun T φ => T φ.1

theorem cmDerivedEval_comap_le :
    MeasurableSpace.comap cmDerivedEval MeasurableSpace.pi ≤ distributionMeasurableSpace := by
  unfold distributionMeasurableSpace
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  refine iSup_le fun φ => ?_
  rw [MeasurableSpace.comap_comp]
  exact le_iSup₂_of_le φ.1 φ.2 le_rfl

theorem cmDerivedEval_measurable : Measurable[distributionMeasurableSpace] cmDerivedEval :=
  measurable_iff_comap_le.2 cmDerivedEval_comap_le

/-- The distribution σ-algebra is the σ-algebra pulled back by `cmDerivedEval` from the product σ-algebra. -/
theorem distributionMeasurableSpace_eq_comap_cmDerivedEval :
    distributionMeasurableSpace = MeasurableSpace.comap cmDerivedEval MeasurableSpace.pi := by
  apply le_antisymm
  · unfold distributionMeasurableSpace
    refine iSup₂_le fun φ hφ => ?_
    have hΨ : Measurable[MeasurableSpace.comap cmDerivedEval MeasurableSpace.pi] cmDerivedEval :=
      comap_measurable cmDerivedEval
    have hev : Measurable[MeasurableSpace.comap cmDerivedEval MeasurableSpace.pi]
        (fun T : (ℂ → ℝ) → ℝ => T φ) :=
      (measurable_pi_apply (⟨φ, hφ⟩ : {φ : ℂ → ℝ // IsTestFunction Set.univ φ})).comp hΨ
    exact hev.comap_le
  · exact cmDerivedEval_comap_le

/-- Cameron-Martin mutual absolute continuity, derived from the reweighting input. -/
theorem cameronMartinGFFMutualAbsCont_of_reweighting
    (hRew : CameronMartinGFFReweighting.{u}) :
    CameronMartinGFFMutualAbsCont.{u} := by
  intro Ω _ P _ hC hcirc g hW hgC hgS hgc B hB
  obtain ⟨P', hP'P, hPP', hW'⟩ := hRew Ω P hC hcirc hW g hgC hgS hgc
  rw [distributionMeasurableSpace_eq_comap_cmDerivedEval] at hB
  obtain ⟨B', hB', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hB
  -- the law of the pairings with test functions, under `P` and under `P'`
  have hmap := wholePlaneGFF_localFieldPairings_map_eq hW hW' 0 Set.univ
  have e1 : localFieldPairings 0 hC Set.univ = fun ω => cmDerivedEval (hC ω) := by
    funext ω φ
    simp [localFieldPairings, fieldPairing, cmDerivedEval]
  have e2 : localFieldPairings 0 (fun ω => addFunPairing (hC ω) g) Set.univ =
      fun ω => cmDerivedEval (addFunPairing (hC ω) g) := by
    funext ω φ
    simp [localFieldPairings, fieldPairing, cmDerivedEval]
  rw [e1, e2] at hmap
  have hF : Measurable fun ω => cmDerivedEval (hC ω) :=
    measurable_pi_iff.2 fun φ => hW.measurable_pairing φ.1 φ.2
  have hF' : Measurable fun ω => cmDerivedEval (addFunPairing (hC ω) g) :=
    measurable_pi_iff.2 fun φ => hW'.measurable_pairing φ.1 φ.2
  have hLHS : P (hC ⁻¹' (cmDerivedEval ⁻¹' B')) = (P.map fun ω => cmDerivedEval (hC ω)) B' :=
    (Measure.map_apply hF hB').symm
  have hRHS : P' ((fun ω => addFunPairing (hC ω) g) ⁻¹' (cmDerivedEval ⁻¹' B')) =
      (P'.map fun ω => cmDerivedEval (addFunPairing (hC ω) g)) B' :=
    (Measure.map_apply hF' hB').symm
  have hEq : P (hC ⁻¹' (cmDerivedEval ⁻¹' B')) =
      P' ((fun ω => addFunPairing (hC ω) g) ⁻¹' (cmDerivedEval ⁻¹' B')) := by
    rw [hLHS, hRHS, hmap]
  constructor
  · intro h0
    have h1 : P' ((fun ω => addFunPairing (hC ω) g) ⁻¹' (cmDerivedEval ⁻¹' B')) = 0 := by
      rw [← hEq]
      exact h0
    exact hPP' h1
  · intro h0
    have h1 : P' ((fun ω => addFunPairing (hC ω) g) ⁻¹' (cmDerivedEval ⁻¹' B')) = 0 := hP'P h0
    rw [← hEq] at h1
    exact h1


/-- Binder-free form: the reweighting input is the theorem `cameronMartinGFFReweighting_derived`. -/
theorem cameronMartinGFFMutualAbsCont_derived : CameronMartinGFFMutualAbsCont.{u} :=
  cameronMartinGFFMutualAbsCont_of_reweighting cameronMartinGFFReweighting_derived

end CMMutualAbsCont

end LatticeProb.Gauss
