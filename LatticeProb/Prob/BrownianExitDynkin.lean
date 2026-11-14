/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/BrownianHarmonicExit.lean
(the passage from truncated to untruncated exit times, harmonic case; extended here by the
Laplacian drift term).
-/

import LatticeProb.Prob.BrownianStoppedDynkin
import LatticeProb.Prob.BrownianPathHarmonicExit

/-!
# Dynkin's formula at the exit time of a bounded open set

For a standard Brownian law `μ` on `BrownianPath d` (`d ≥ 1`), a bounded open set `U`, a starting
point `z` and a `C²` function `f` with compact support, with `τ` the exit time of the shifted path
`t ↦ z + ω t` from `U`:
`∫ f (z + ω τ) ∂μ - f z = (1 / 2) ∫ ∫_0^τ Δ f (z + ω u) du ∂μ`.

The mean exit time is finite: Dynkin's formula at `τ ∧ N` for a compactly supported function
equal to `‖x‖ ²` near `U` (whose Laplacian is `2 d` there) bounds `E (τ ∧ N)` uniformly in `N`.
Then both sides of Dynkin's formula at `τ ∧ N` converge as `N → ∞` by dominated convergence, with
the bounds `2 sup |f|` and `sup |Δ f| · τ`.

## Main results

* `laplacian_norm_sq_euc`: `Δ ‖x‖ ² = 2 d`.
* `stronglyMeasurable_intervalIntegral_path`: measurability of `ω ↦ ∫_0^σ(ω) G (z + ω u) du`.
* `standardBrownianLaw_truncated_exit_dynkin`: Dynkin's formula at `τ ∧ N`.
* `standardBrownianLaw_lintegral_continuousExitTime_lt_top`: `E τ < ∞` for bounded `U`.
* `standardBrownianLaw_exit_dynkin`: Dynkin's formula at `τ`.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Laplacian Set Filter
open scoped NNReal ENNReal Topology Interval

namespace LatticeProb

/-- The Laplacian of the squared norm on `Euc d` is the constant `2 d`. -/
theorem laplacian_norm_sq_euc {d : ℕ} (x : Euc d) :
    Δ (fun y : Euc d ↦ ‖y‖ ^ 2) x = 2 * d := by
  have hdiff : Differentiable ℝ (fderiv ℝ (fun y : Euc d ↦ ‖y‖ ^ 2)) :=
    ((contDiff_norm_sq ℝ (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)
  have hdir (v : Euc d) :
      fderiv ℝ (fderiv ℝ (fun y : Euc d ↦ ‖y‖ ^ 2)) x v v = 2 * inner ℝ v v := by
    have h1 : (fun y ↦ fderiv ℝ (fun y : Euc d ↦ ‖y‖ ^ 2) y v) =
        ⇑((2 : ℝ) • innerSL ℝ v) := by
      funext y
      simp [fderiv_norm_sq_apply, real_inner_comm]
    have hA : HasFDerivAt (fun y ↦ fderiv ℝ (fun y : Euc d ↦ ‖y‖ ^ 2) y v)
        ((2 : ℝ) • innerSL ℝ v) x := by
      rw [h1]
      exact ContinuousLinearMap.hasFDerivAt _
    have hB := (hdiff x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
    have h := congrArg (fun L : Euc d →L[ℝ] ℝ ↦ L v) (hA.unique hB)
    simpa using h.symm
  rw [laplacian_eq_sum_fderiv_fderiv_basisFun]
  simp only [hdir]
  simp [mul_comm]

/-- A `C²` function with compact support whose Laplacian equals `2 d` on a given bounded set: a
smooth cut-off of `‖x‖ ²`. -/
theorem exists_contDiff_hasCompactSupport_laplacian_eq_two_mul_dim {d : ℕ} {U : Set (Euc d)}
    (hUb : Bornology.IsBounded U) :
    ∃ f : Euc d → ℝ, ContDiff ℝ 2 f ∧ HasCompactSupport f ∧ ∀ x ∈ U, Δ f x = 2 * d := by
  obtain ⟨R, hR⟩ := hUb.subset_closedBall (0 : Euc d)
  let φ : ContDiffBump (0 : Euc d) := ⟨|R| + 1, |R| + 2, by positivity, by linarith⟩
  refine ⟨fun y ↦ φ y * ‖y‖ ^ 2, φ.contDiff.mul (contDiff_norm_sq ℝ),
    φ.hasCompactSupport.mul_right, fun x hx ↦ ?_⟩
  have hx' : x ∈ Metric.ball (0 : Euc d) (|R| + 1) := by
    have h := hR hx
    rw [Metric.mem_closedBall] at h
    rw [Metric.mem_ball]
    linarith [le_abs_self R]
  have heq : (fun y ↦ φ y * ‖y‖ ^ 2) =ᶠ[𝓝 x] fun y ↦ ‖y‖ ^ 2 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hx'] with y hy
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall hy), one_mul]
  rw [(laplacian_congr_nhds heq).eq_of_nhds, laplacian_norm_sq_euc]

/-- For a continuous `G` and a measurable random time `σ`, the time integral
`ω ↦ ∫_0^σ(ω) G (z + ω u) du` along the shifted path is strongly measurable. -/
theorem stronglyMeasurable_intervalIntegral_path {d : ℕ} {G : Euc d → ℝ} (hG : Continuous G)
    {σ : BrownianPath d → ℝ≥0} (hσ : Measurable σ) (z : Euc d) :
    StronglyMeasurable
      (fun ω : BrownianPath d ↦ ∫ u in (0 : ℝ)..(σ ω : ℝ), G (z + ω u.toNNReal)) := by
  let S : Set (BrownianPath d × ℝ) := {q | 0 < q.2} ∩ {q | q.2 ≤ (σ q.1 : ℝ)}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd
        (NNReal.continuous_coe.measurable.comp (hσ.comp measurable_fst)))
  have hcont : Continuous (fun q : BrownianPath d × ℝ ↦ G (z + q.1 q.2.toNNReal)) :=
    hG.comp (continuous_const.add (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))))
  have hF : StronglyMeasurable
      (S.indicator (fun q : BrownianPath d × ℝ ↦ G (z + q.1 q.2.toNNReal))) :=
    (hcont.measurable.indicator hS).stronglyMeasurable
  have h := hF.integral_prod_right' (ν := (volume : Measure ℝ))
  convert h using 2 with ω
  rw [intervalIntegral.integral_of_le (NNReal.coe_nonneg _),
    ← integral_indicator measurableSet_Ioc]
  refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
  dsimp only
  by_cases hu : u ∈ Ioc (0 : ℝ) (σ ω)
  · rw [indicator_of_mem hu, indicator_of_mem (show (ω, u) ∈ S from hu)]
  · rw [indicator_of_notMem hu, indicator_of_notMem (show (ω, u) ∉ S from hu)]

/-- Dynkin's formula at the exit time of an open set `U` from the shifted path `t ↦ z + ω t`,
truncated at `N`. -/
theorem standardBrownianLaw_truncated_exit_dynkin {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {U : Set (Euc d)} (hU : IsOpen U) (N : ℝ≥0) (z : Euc d) :
    (∫ ω, f (z + ω (min (continuousExitTime U z ω) (N : ℝ≥0∞)).toNNReal) - f (z + ω 0) ∂μ) =
      (1 / 2 : ℝ) * ∫ ω, (∫ u in (0 : ℝ)..((min (continuousExitTime U z ω) (N : ℝ≥0∞)).toNNReal : ℝ),
        Δ f (z + ω u.toNNReal)) ∂μ := by
  have hfin (ω : BrownianPath d) : min (continuousExitTime U z ω) (N : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hcoe : (fun ω ↦ ((ENNReal.toNNReal (min (continuousExitTime U z ω) N) : ℝ≥0) :
      ℝ≥0∞)) = fun ω ↦ min (continuousExitTime U z ω) (N : ℝ≥0∞) :=
    funext fun ω ↦ ENNReal.coe_toNNReal (hfin ω)
  have hσ : IsStoppingTime (brownianNaturalFiltration d)
      (fun ω ↦ ((ENNReal.toNNReal (min (continuousExitTime U z ω) N) : ℝ≥0) : ℝ≥0∞)) := by
    rw [hcoe]
    exact (isStoppingTime_continuousExitTime hU z).min_const N
  refine standardBrownianLaw_bounded_stopped_dynkin hμ hf hsupp hσ N (fun ω ↦ ?_) z
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (hfin ω)]
  exact min_le_right _ _

/-- The mean exit time of the shifted Brownian path from a bounded open set is finite. -/
theorem standardBrownianLaw_lintegral_continuousExitTime_lt_top {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (z : Euc d) :
    ∫⁻ ω, continuousExitTime U z ω ∂μ < ∞ := by
  have : IsProbabilityMeasure μ := hμ.1
  obtain ⟨f, hf, hsupp, hΔ⟩ := exists_contDiff_hasCompactSupport_laplacian_eq_two_mul_dim hUb
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hf.continuous
  have hd0 : (0 : ℝ) < d := Nat.cast_pos.mpr (by omega)
  let τ : BrownianPath d → ℝ≥0∞ := continuousExitTime U z
  have hτm : Measurable τ := measurable_continuousExitTime hU z
  have hbound (n : ℕ) :
      ∫⁻ ω, min (τ ω) ((n : ℝ≥0) : ℝ≥0∞) ∂μ ≤ ENNReal.ofReal (2 * M / d) := by
    let σ : BrownianPath d → ℝ≥0 := fun ω ↦ (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal
    have hfin (ω : BrownianPath d) : min (τ ω) ((n : ℝ≥0) : ℝ≥0∞) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
    have hσm : Measurable σ := ENNReal.measurable_toNNReal.comp (hτm.min measurable_const)
    have hσle (ω : BrownianPath d) : σ ω ≤ (n : ℝ≥0) := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (hfin ω)]
      exact min_le_right _ _
    have hσint : Integrable (fun ω ↦ (σ ω : ℝ)) μ :=
      (integrable_const ((n : ℝ≥0) : ℝ)).mono'
        (NNReal.continuous_coe.measurable.comp hσm).aestronglyMeasurable
        (Eventually.of_forall fun ω ↦ by
          rw [Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)]
          exact_mod_cast hσle ω)
    have htime (ω : BrownianPath d) :
        ∫ u in (0 : ℝ)..(σ ω : ℝ), Δ f (z + ω u.toNNReal) = 2 * d * σ ω := by
      have h : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Ι (0 : ℝ) (σ ω) →
          Δ f (z + ω u.toNNReal) = 2 * d := by
        filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (σ ω : ℝ))] with u hu hmem
        rw [Set.uIoc_of_le (NNReal.coe_nonneg _)] at hmem
        have hlt : u < σ ω := lt_of_le_of_ne hmem.2 hu
        apply hΔ
        apply mem_of_lt_continuousExitTime
        have h1 : u.toNNReal < σ ω := (Real.toNNReal_lt_iff_lt_coe hmem.1.le).mpr hlt
        calc (u.toNNReal : ℝ≥0∞) < σ ω := ENNReal.coe_lt_coe.mpr h1
          _ = min (τ ω) ((n : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_toNNReal (hfin ω)
          _ ≤ τ ω := min_le_left _ _
      rw [intervalIntegral.integral_congr_ae h, intervalIntegral.integral_const, smul_eq_mul,
        sub_zero]
      ring
    have hdyn : (∫ ω, f (z + ω (σ ω)) - f (z + ω 0) ∂μ) =
        (1 / 2 : ℝ) * ∫ ω, (∫ u in (0 : ℝ)..(σ ω : ℝ), Δ f (z + ω u.toNNReal)) ∂μ :=
      standardBrownianLaw_truncated_exit_dynkin hμ hf hsupp hU (n : ℝ≥0) z
    have hJ : (∫ ω, (∫ u in (0 : ℝ)..(σ ω : ℝ), Δ f (z + ω u.toNNReal)) ∂μ) =
        2 * d * ∫ ω, (σ ω : ℝ) ∂μ :=
      (integral_congr_ae (Eventually.of_forall htime)).trans (integral_const_mul _ _)
    rw [hJ] at hdyn
    have hg : |∫ ω, f (z + ω (σ ω)) - f (z + ω 0) ∂μ| ≤ 2 * M := by
      have hb (ω : BrownianPath d) : ‖f (z + ω (σ ω)) - f (z + ω 0)‖ ≤ 2 * M :=
        (norm_sub_le _ _).trans (by linarith [hM (z + ω (σ ω)), hM (z + ω 0)])
      have h := norm_integral_le_of_norm_le_const (μ := μ) (Eventually.of_forall hb)
      simpa using h
    have hσI : ∫ ω, (σ ω : ℝ) ∂μ ≤ 2 * M / d := by
      rw [le_div_iff₀ hd0]
      have h := le_abs_self (∫ ω, f (z + ω (σ ω)) - f (z + ω 0) ∂μ)
      nlinarith
    calc ∫⁻ ω, min (τ ω) ((n : ℝ≥0) : ℝ≥0∞) ∂μ = ∫⁻ ω, (σ ω : ℝ≥0∞) ∂μ :=
          lintegral_congr fun ω ↦ (ENNReal.coe_toNNReal (hfin ω)).symm
      _ = ENNReal.ofReal (∫ ω, (σ ω : ℝ) ∂μ) := lintegral_coe_eq_integral σ hσint
      _ ≤ ENNReal.ofReal (2 * M / d) := ENNReal.ofReal_le_ofReal hσI
  have hmono : Monotone (fun (n : ℕ) (ω : BrownianPath d) ↦ min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)) := by
    intro m n hmn ω
    exact min_le_min_left _ (ENNReal.coe_le_coe.mpr (Nat.cast_le.mpr hmn))
  have hsup (ω : BrownianPath d) : (⨆ n : ℕ, min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)) = τ ω := by
    refine le_antisymm (iSup_le fun n ↦ min_le_left _ _) (le_of_forall_lt fun c hc ↦ ?_)
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hc)
    refine lt_of_lt_of_le ?_ (le_iSup _ n)
    show c < min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)
    rw [ENNReal.coe_natCast]
    exact lt_min hc hn
  calc ∫⁻ ω, continuousExitTime U z ω ∂μ
      = ∫⁻ ω, ⨆ n : ℕ, min (τ ω) ((n : ℝ≥0) : ℝ≥0∞) ∂μ :=
        lintegral_congr fun ω ↦ (hsup ω).symm
    _ = ⨆ n : ℕ, ∫⁻ ω, min (τ ω) ((n : ℝ≥0) : ℝ≥0∞) ∂μ :=
        lintegral_iSup (fun _ ↦ hτm.min measurable_const) hmono
    _ ≤ ENNReal.ofReal (2 * M / d) := iSup_le hbound
    _ < ∞ := ENNReal.ofReal_lt_top

/-- **Dynkin's formula at the exit time.** For a standard Brownian law in dimension at least one,
a bounded open set `U`, a starting point `z` and a `C²` function `f` with compact support, with
`τ` the exit time of the shifted path `t ↦ z + ω t` from `U`:
`E f (z + ω τ) - f z = (1 / 2) E ∫_0^τ Δ f (z + ω u) du`. -/
theorem standardBrownianLaw_exit_dynkin {d : ℕ} (hd : 1 ≤ d)
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ)
    {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (hsupp : HasCompactSupport f)
    {U : Set (Euc d)} (hU : IsOpen U) (hUb : Bornology.IsBounded U) (z : Euc d) :
    (∫ ω, f (z + ω (continuousExitTime U z ω).toNNReal) ∂μ) - f z =
      (1 / 2 : ℝ) * ∫ ω, (∫ u in (0 : ℝ)..((continuousExitTime U z ω).toNNReal : ℝ),
        Δ f (z + ω u.toNNReal)) ∂μ := by
  have : IsProbabilityMeasure μ := hμ.1
  let τ : BrownianPath d → ℝ≥0∞ := continuousExitTime U z
  have hτm : Measurable τ := measurable_continuousExitTime hU z
  let σ : ℕ → BrownianPath d → ℝ≥0 := fun n ω ↦ (min (τ ω) ((n : ℝ≥0) : ℝ≥0∞)).toNNReal
  have hσm (n : ℕ) : Measurable (σ n) :=
    ENNReal.measurable_toNNReal.comp (hτm.min measurable_const)
  let J : ℕ → BrownianPath d → ℝ := fun n ω ↦
    ∫ u in (0 : ℝ)..(σ n ω : ℝ), Δ f (z + ω u.toNNReal)
  let J' : BrownianPath d → ℝ := fun ω ↦
    ∫ u in (0 : ℝ)..((τ ω).toNNReal : ℝ), Δ f (z + ω u.toNNReal)
  have hΔc : Continuous (Δ f) := continuous_laplacian_of_contDiff_two hf
  obtain ⟨M', hM'⟩ := exists_bound_laplacian_of_contDiff_compactSupport hf hsupp
  have hM'0 : 0 ≤ M' := (norm_nonneg _).trans (hM' 0)
  obtain ⟨M, hM⟩ := hsupp.exists_bound_of_continuous hf.continuous
  have hmean (n : ℕ) :
      (∫ ω, f (z + ω (σ n ω)) - f (z + ω 0) ∂μ) = (1 / 2 : ℝ) * ∫ ω, J n ω ∂μ :=
    standardBrownianLaw_truncated_exit_dynkin hμ hf hsupp hU (n : ℝ≥0) z
  have hfinite : ∀ᵐ ω ∂μ, τ ω ≠ ∞ := standardBrownianLaw_ae_finiteExit hd hμ hUb z
  have hev : ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, σ n ω = (τ ω).toNNReal := by
    filter_upwards [hfinite] with ω hω
    obtain ⟨N, hN⟩ := exists_nat_gt ((τ ω).toNNReal : ℝ)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hle : τ ω ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
      rw [← ENNReal.coe_toNNReal hω]
      have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hreal : ((τ ω).toNNReal : ℝ) ≤ ((n : ℝ≥0) : ℝ) := by
        simpa only [NNReal.coe_natCast] using hN.le.trans hNn
      exact ENNReal.coe_le_coe.mpr (NNReal.coe_le_coe.mp hreal)
    simp only [σ, min_eq_left hle]
  have hmzero : Measurable (fun ω : BrownianPath d ↦ f (z + ω 0)) :=
    hf.continuous.measurable.comp
      (measurable_const.add (continuous_eval_const (0 : ℝ≥0)).measurable)
  have hmseq (n : ℕ) : Measurable (fun ω : BrownianPath d ↦ f (z + ω (σ n ω))) :=
    hf.continuous.measurable.comp
      (measurable_const.add (measurable_brownian_random_evaluation (hσm n)))
  have hmexit : Measurable (fun ω : BrownianPath d ↦ f (z + ω (τ ω).toNNReal)) :=
    hf.continuous.measurable.comp (measurable_const.add
      (measurable_brownian_random_evaluation (ENNReal.measurable_toNNReal.comp hτm)))
  have hL : Tendsto (fun n ↦ ∫ ω, f (z + ω (σ n ω)) - f (z + ω 0) ∂μ) atTop
      (𝓝 (∫ ω, f (z + ω (τ ω).toNNReal) - f (z + ω 0) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ 2 * M)
      (fun n ↦ ((hmseq n).sub hmzero).aestronglyMeasurable) (integrable_const _)
      (fun n ↦ ?_) ?_
    · exact Eventually.of_forall fun ω ↦ (norm_sub_le _ _).trans
        (by linarith [hM (z + ω (σ n ω)), hM (z + ω 0)])
    · filter_upwards [hev] with ω hω
      exact tendsto_const_nhds.congr' (hω.mono fun n hn ↦ by simp only [hn])
  have hτint : Integrable (fun ω ↦ (τ ω).toReal) μ :=
    integrable_toReal_of_lintegral_ne_top hτm.aemeasurable
      (standardBrownianLaw_lintegral_continuousExitTime_lt_top hd hμ hU hUb z).ne
  have hR : Tendsto (fun n ↦ ∫ ω, J n ω ∂μ) atTop (𝓝 (∫ ω, J' ω ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun ω ↦ M' * (τ ω).toReal)
      (fun n ↦ (stronglyMeasurable_intervalIntegral_path hΔc (hσm n) z).aestronglyMeasurable)
      (hτint.const_mul M') (fun n ↦ ?_) ?_
    · filter_upwards [hfinite] with ω hω
      have hστ : (σ n ω : ℝ) ≤ (τ ω).toReal := by
        have h1 : σ n ω ≤ (τ ω).toNNReal := ENNReal.toNNReal_mono hω (min_le_left _ _)
        rw [← ENNReal.coe_toNNReal_eq_toReal]
        exact NNReal.coe_le_coe.mpr h1
      calc ‖J n ω‖ ≤ M' * |(σ n ω : ℝ) - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const fun u _ ↦ hM' _
        _ ≤ M' * (τ ω).toReal := by
            rw [sub_zero, abs_of_nonneg (NNReal.coe_nonneg _)]
            exact mul_le_mul_of_nonneg_left hστ hM'0
    · filter_upwards [hev] with ω hω
      exact tendsto_const_nhds.congr' (hω.mono fun n hn ↦ by simp only [J, J', hn])
  have hlim2 : Tendsto (fun n ↦ ∫ ω, f (z + ω (σ n ω)) - f (z + ω 0) ∂μ) atTop
      (𝓝 ((1 / 2 : ℝ) * ∫ ω, J' ω ∂μ)) := by
    simp only [hmean]
    exact hR.const_mul _
  have hdiff := tendsto_nhds_unique hL hlim2
  have hiexit : Integrable (fun ω ↦ f (z + ω (τ ω).toNNReal)) μ :=
    (integrable_const M).mono' hmexit.aestronglyMeasurable (Eventually.of_forall fun ω ↦ hM _)
  have hizero : Integrable (fun ω : BrownianPath d ↦ f (z + ω 0)) μ :=
    (integrable_const M).mono' hmzero.aestronglyMeasurable (Eventually.of_forall fun ω ↦ hM _)
  have hbase : (∫ ω, f (z + ω 0) ∂μ) = f z := by
    have heq : (fun ω : BrownianPath d ↦ f (z + ω 0)) =ᵐ[μ] fun _ ↦ f z :=
      (standardBrownianLaw_eval_zero_ae hμ).mono (fun ω hω ↦ by
        change f (z + ω 0) = f z
        rw [hω, add_zero])
    rw [integral_congr_ae heq]
    simp
  have heq := integral_sub hiexit hizero
  change (∫ ω, f (z + ω (τ ω).toNNReal) - f (z + ω 0) ∂μ) =
    (∫ ω, f (z + ω (τ ω).toNNReal) ∂μ) - (∫ ω, f (z + ω 0) ∂μ) at heq
  rw [heq, hbase] at hdiff
  exact hdiff

end LatticeProb
